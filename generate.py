#!/usr/bin/env python3
# pylint: disable=line-too-long

import sys
import argparse
import random
import json
import asyncio
import time
import re
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Any, Set
from faker import Faker  # type: ignore
from geopy.geocoders import Nominatim  # type: ignore
from geopy.location import Location  # type: ignore
from geopy.adapters import AioHTTPAdapter  # type: ignore

try:
    import us  # type: ignore
except ImportError:
    print(
        "Error: 'us' library not installed.",
        file=sys.stderr,
    )
    sys.exit(1)

# File paths
_CACHE_FILE = Path(__file__).parent / ".cache.json"
_CITIES_FILE = Path(__file__).parent / "cities.json"

# Geocoding API settings
_GEOCODE_TIMEOUT = 15
# Separate limits for different operation types to allow intermingling
_MAX_CONCURRENT_CITY_FETCHES = 5  # Limit concurrent city boundary fetches
_MAX_CONCURRENT_REVERSE_GEOCODE = 10  # Limit concurrent reverse geocoding calls

# Address lookup settings
_ADDRESS_BATCH_SIZE = 1  # How many coordinates to try simultaneously
_MAX_ADDRESS_BATCHES = 10  # How many batches to try before giving up
_MAX_CITIES_TO_TRY = 3  # How many different cities to try before giving up

# Rate limiting - configurable calls per time window
_MAX_CALLS_PER_WINDOW = 5  # Maximum calls allowed in the window
_WINDOW_SECONDS = 5.0  # Time window in seconds

# Data generation settings
_AGE_RANGE = (23, 45)  # (min_age, max_age)
_DEFAULT_NUM_RECORDS = 3  # Default number of records to generate if not specified

# Type aliases
BoundingBox = Tuple[float, float, float, float]  # (min_lat, max_lat, min_lon, max_lon)
CityCache = Dict[str, Dict[str, BoundingBox]]  # {state_code: {city_name: bbox}}

# Cache for city bounding boxes to avoid repeated API calls
_city_cache: CityCache = {}

# Track which cities are currently being fetched per state
# state_code -> set of city names being fetched
_in_flight_cities: Dict[str, Set[str]] = {}
_in_flight_lock = asyncio.Lock()  # Lock for coordinating in-flight requests

# API call counters for tracking efficiency
_api_stats = {
    "geocoding_calls": 0,
    "geocoding_successes": 0,
    "geocoding_failures": 0,
    "reverse_geocoding_calls": 0,
    "reverse_geocoding_successes": 0,
    "reverse_geocoding_failures": 0,
    "successful_records": 0,
}


def load_city_cache() -> None:
    """Load city cache from file.

    Cache format: {state_code: {city_name: [min_lat, max_lat, min_lon, max_lon], ...}}
    Supports backward compatibility with old format: {state_code: [[bbox], ...]}
    """
    global _city_cache
    if not _CACHE_FILE.exists():
        _city_cache = {}
        return

    try:
        with open(_CACHE_FILE, "r", encoding="utf-8") as f:
            data: Dict[str, Any] = json.load(f)
            _city_cache = {}
            for state_code, cities_data in data.items():
                if isinstance(cities_data, dict):
                    # New format: {city_name: [bbox], ...}
                    _city_cache[state_code] = {
                        city_name: tuple(bbox)  # type: ignore
                        for city_name, bbox in cities_data.items()
                    }
                elif isinstance(cities_data, list):
                    # Old format: [[bbox], ...] - migrate to new format
                    # We can't recover city names, so we'll use empty dict
                    # and let it re-fetch with names
                    _city_cache[state_code] = {}
    except (json.JSONDecodeError, IOError):
        # If file is corrupted or can't be read, start with empty cache
        _city_cache = {}


def save_city_cache() -> None:
    """Save city cache to file.

    Cache format: {state_code: {city_name: [min_lat, max_lat, min_lon, max_lon], ...}}
    """
    try:
        # Convert tuples to lists for JSON serialization
        data = {
            state_code: {city_name: list(bbox) for city_name, bbox in cities.items()}
            for state_code, cities in _city_cache.items()
        }
        # Use atomic write: write to temp file then rename
        temp_file = _CACHE_FILE.with_suffix(".tmp")
        with open(temp_file, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2)
        temp_file.replace(_CACHE_FILE)
    except (IOError, OSError) as e:
        # Log error but don't crash
        print(f"Warning: Could not save cache: {e}", file=sys.stderr)


# Load cache at startup
load_city_cache()


def load_major_cities() -> Dict[str, List[str]]:
    """Load major cities from city data file."""
    if not _CITIES_FILE.exists():
        print(
            f"Error: Cities file {_CITIES_FILE} not found. "
            "Please create it with city data.",
            file=sys.stderr,
        )
        sys.exit(1)

    try:
        with open(_CITIES_FILE, "r", encoding="utf-8") as f:
            cities = json.load(f)
            # Validate structure
            if not isinstance(cities, dict):
                print(
                    f"Error: Invalid format in {_CITIES_FILE}: expected dict",
                    file=sys.stderr,
                )
                sys.exit(1)
            if not all(
                isinstance(v, list) and all(isinstance(c, str) for c in v)
                for v in cities.values()
            ):
                print(
                    f"Error: Invalid format in {_CITIES_FILE}: "
                    "expected dict of string lists",
                    file=sys.stderr,
                )
                sys.exit(1)
            return cities
    except json.JSONDecodeError as e:
        print(
            f"Error: Invalid JSON in {_CITIES_FILE}: {e}",
            file=sys.stderr,
        )
        sys.exit(1)
    except IOError as e:
        print(
            f"Error: Could not read {_CITIES_FILE}: {e}",
            file=sys.stderr,
        )
        sys.exit(1)


# Major cities by state code for more reliable city selection
MAJOR_CITIES = load_major_cities()


# Single queue-based rate limiter for all API calls
# All API calls go through a single queue with rate limiting
_api_queue: Optional[asyncio.Queue] = None
_api_queue_worker: Optional[asyncio.Task] = None
# Track timestamps of recent API calls for sliding window
_api_call_times: List[float] = []
_api_call_times_lock = asyncio.Lock()  # Lock for protecting _api_call_times
_geolocator: Optional[Nominatim] = None  # Shared async geolocator instance
_api_queue_init_lock = asyncio.Lock()  # Lock for queue worker initialization
_debug_mode = False  # Whether to print debug messages and API call summary


class RateLimiter:
    """Unified rate limiter using a single queue.

    Enforces rate limiting based on _MAX_CALLS_PER_WINDOW and _WINDOW_SECONDS,
    and intermingles calls.
    """

    def __init__(
        self,
        max_concurrent_city_fetches: int,
        max_concurrent_reverse_geocode: int,
    ):
        # Semaphores for concurrency control (not rate limiting)
        self._city_fetch_semaphore = asyncio.Semaphore(max_concurrent_city_fetches)
        self._reverse_geocode_semaphore = asyncio.Semaphore(
            max_concurrent_reverse_geocode
        )
        # Queue worker will be initialized lazily when first needed

    async def _ensure_queue_worker(self):
        """Ensure the API queue worker is running."""
        global _api_queue, _api_queue_worker, _api_queue_init_lock
        async with _api_queue_init_lock:
            if _api_queue is None:
                _api_queue = asyncio.Queue()
            if _api_queue_worker is None or _api_queue_worker.done():
                _api_queue_worker = asyncio.create_task(self._queue_worker())

    async def _queue_worker(self):
        """Worker that processes API calls with rate limiting.

        Starts API calls at the configured rate (based on _MAX_CALLS_PER_WINDOW
        and _WINDOW_SECONDS), but doesn't wait for them to complete. This allows
        multiple calls to be in-flight simultaneously while maintaining the rate
        limit on when calls are started.
        """
        global _api_call_times, _api_call_times_lock, _geolocator, _api_queue_init_lock

        # Initialize async geolocator if not already done (with lock to prevent race)
        async with _api_queue_init_lock:
            if _geolocator is None:
                try:
                    _geolocator = Nominatim(
                        user_agent="identity-address-generator",
                        adapter_factory=AioHTTPAdapter,
                    )
                    await _geolocator.__aenter__()  # Initialize async context
                except Exception as e:
                    # If initialization fails, set to None and re-raise
                    _geolocator = None
                    raise RuntimeError(f"Failed to initialize geolocator: {e}") from e

        async def _execute_and_set_result(future, call_type, *args):
            """Execute async API call and set future result when done."""
            global _debug_mode
            try:
                if _geolocator is None:
                    raise RuntimeError("Geolocator not initialized")

                if call_type == "geocode":
                    query = args[0]
                    if _debug_mode:
                        timestamp = time.strftime("%H:%M:%S", time.localtime())
                        milliseconds = int(time.time() * 1000) % 1000
                        timestamp = f"{timestamp}.{milliseconds:03d}"
                        print(
                            f"DEBUG: [{timestamp}] Geocoding API call: {query}",
                            file=sys.stderr,
                        )
                    result = await _geolocator.geocode(query, timeout=_GEOCODE_TIMEOUT)
                elif call_type == "reverse":
                    lat, lon = args[0], args[1]
                    if _debug_mode:
                        timestamp = time.strftime("%H:%M:%S", time.localtime())
                        milliseconds = int(time.time() * 1000) % 1000
                        timestamp = f"{timestamp}.{milliseconds:03d}"
                        print(
                            f"DEBUG: [{timestamp}] Reverse geocoding API call: "
                            f"({lat:.6f}, {lon:.6f})",
                            file=sys.stderr,
                        )
                    result = await _geolocator.reverse(
                        (lat, lon), timeout=_GEOCODE_TIMEOUT
                    )
                else:
                    raise ValueError(f"Unknown call type: {call_type}")

                if not future.done():
                    future.set_result(result)
            except Exception as e:
                if not future.done():
                    future.set_exception(e)
            finally:
                _api_queue.task_done()

        while True:
            future = None
            try:
                # Get next API call from queue
                item = await _api_queue.get()
                if item is None:  # Sentinel to stop worker
                    _api_queue.task_done()  # Mark sentinel as processed
                    break

                future, call_type, args = item

                # Enforce rate limit on STARTING calls (sliding window)
                current_time = time.time()
                async with _api_call_times_lock:
                    # Remove timestamps older than the window
                    cutoff_time = current_time - _WINDOW_SECONDS
                    _api_call_times = [t for t in _api_call_times if t > cutoff_time]

                    # If at limit, wait until oldest call is outside the window
                    if len(_api_call_times) >= _MAX_CALLS_PER_WINDOW:
                        oldest_call_time = min(_api_call_times)
                        wait_time = _WINDOW_SECONDS - (current_time - oldest_call_time)
                        if wait_time > 0:
                            await asyncio.sleep(wait_time)
                            current_time = time.time()
                            # Re-filter after waiting
                            cutoff_time = current_time - _WINDOW_SECONDS
                            _api_call_times = [
                                t for t in _api_call_times if t > cutoff_time
                            ]

                    # Record this call time
                    _api_call_times.append(current_time)

                # Start the async API call but don't wait for it to complete
                # This allows the worker to process the next queue item immediately
                # No threads needed - this is true async I/O!
                asyncio.create_task(_execute_and_set_result(future, call_type, *args))

            except asyncio.CancelledError:
                break
            except Exception as e:
                # We got an item from the queue, so we must call task_done()
                # even if we didn't create a task for it
                if future is not None and not future.done():
                    future.set_exception(e)
                # Always call task_done() since we called get()
                _api_queue.task_done()

    async def _execute_via_queue(self, call_type: str, *args):
        """Execute an async API call via the queue."""
        global _api_queue
        # Initialize queue worker lazily when event loop is running
        await self._ensure_queue_worker()
        future = asyncio.get_running_loop().create_future()
        await _api_queue.put((future, call_type, args))
        return await future

    async def execute_city_fetch(self, query: str):
        """Execute a city geocoding call with rate limiting via queue."""
        await self._city_fetch_semaphore.acquire()
        try:
            try:
                result = await self._execute_via_queue("geocode", query)
            except Exception:
                result = None
        finally:
            self._city_fetch_semaphore.release()
        return result

    async def execute_reverse_geocode(self, lat: float, lon: float):
        """Execute a reverse geocoding call with rate limiting via queue."""
        await self._reverse_geocode_semaphore.acquire()
        try:
            try:
                result = await self._execute_via_queue("reverse", lat, lon)
            except Exception:
                result = None
        finally:
            self._reverse_geocode_semaphore.release()
        return result


async def _geocode_city_async(
    query: str,
    rate_limiter: RateLimiter,
) -> Optional[Location]:
    """Async geocoding for a city - uses true async I/O."""
    _api_stats["geocoding_calls"] += 1
    result = await rate_limiter.execute_city_fetch(query)
    if result:
        _api_stats["geocoding_successes"] += 1
    else:
        _api_stats["geocoding_failures"] += 1
    return result


async def _reverse_geocode_async(
    lat: float,
    lon: float,
    rate_limiter: RateLimiter,
) -> Optional[Location]:
    """Async reverse geocoding - uses true async I/O."""
    _api_stats["reverse_geocoding_calls"] += 1
    result = await rate_limiter.execute_reverse_geocode(lat, lon)
    if not result:
        _api_stats["reverse_geocoding_failures"] += 1
    return result


def _parse_bounding_box(location: Location) -> Optional[BoundingBox]:
    """Extract bounding box from a Location object."""
    try:
        if not (
            hasattr(location, "raw") and "boundingbox" in location.raw  # type: ignore
        ):
            return None
        bbox = location.raw["boundingbox"]  # type: ignore
        return (
            float(bbox[0]),
            float(bbox[1]),
            float(bbox[2]),
            float(bbox[3]),
        )
    except (AttributeError, ValueError, IndexError, TypeError):
        return None


async def _get_cities_async(
    state_code: str,
    state_name: str,
    city_names: List[str],
    rate_limiter: RateLimiter,
) -> Dict[str, BoundingBox]:
    """Async function to geocode multiple cities in parallel.

    Returns: dict mapping city_name -> (min_lat, max_lat, min_lon, max_lon)
    """
    cities: Dict[str, BoundingBox] = {}

    # Create tasks for all city geocoding calls
    tasks = []
    city_name_list: List[str] = []  # Keep track of order to match results
    for city_name in city_names:
        # For DC, use a more specific query format that works better
        # with geocoding services
        if state_code == "DC":
            # Use "Washington, District of Columbia, USA" for unambiguous
            # results - avoids confusion with Washington state
            query = f"{city_name}, District of Columbia, USA"
        else:
            query = f"{city_name}, {state_name}, USA"
        tasks.append(_geocode_city_async(query, rate_limiter))
        city_name_list.append(city_name)

    # Run all geocoding calls in parallel
    results = await asyncio.gather(*tasks, return_exceptions=True)

    # Process results - collect ALL valid cities
    for city_name, result in zip(city_name_list, results):
        if isinstance(result, Exception):
            continue
        if not result:
            continue

        bbox = _parse_bounding_box(result)
        if bbox:
            cities[city_name] = bbox

    return cities


async def _fetch_city_bbox_async(
    state_code: str,
    state_name: str,
    rate_limiter: RateLimiter,
    city_to_fetch: Optional[str] = None,
) -> BoundingBox:
    """Fetch a specific city for a state and cache it.

    Args:
        rate_limiter: Rate limiter for API calls.
        city_to_fetch: Specific city name to fetch. If None, falls back to state name.
    """
    # city_to_fetch should always be provided, but handle None for safety
    if city_to_fetch is None:
        raise ValueError("city_to_fetch must be provided")

    # Fetch the specific city
    new_cities = await _get_cities_async(
        state_code, state_name, [city_to_fetch], rate_limiter
    )

    # Merge new cities with current cache state (not stale existing_cities)
    # This prevents race conditions where concurrent requests overwrite each other
    async with _in_flight_lock:
        current_cities = _city_cache.get(state_code, {}).copy()
        all_cities = {**current_cities, **new_cities}
        _city_cache[state_code] = all_cities
        save_city_cache()

    if not all_cities:
        raise ValueError(f"Could not geocode city '{city_to_fetch}' for {state_name}")

    return random.choice(list(all_cities.values()))


def _get_state_name(state_code: str) -> str:
    """Get state name from state code, handling DC specially."""
    try:
        state = us.states.lookup(state_code)
        if not state:
            raise ValueError(f"Invalid state code: {state_code}")
        return state.name
    except Exception:
        # Handle DC specially
        if state_code == "DC":
            return "District of Columbia"
        raise ValueError(f"Invalid state code: {state_code}")


def _get_total_available_cities(state_code: str) -> int:
    """Get total number of cities available for a state."""
    total = len(MAJOR_CITIES.get(state_code, []))
    return total if total > 0 else 1


async def get_random_city_bbox_async(
    state_code: str, rate_limiter: RateLimiter
) -> BoundingBox:
    """Get a random city's bounding box from a state using Nominatim (async).

    Uses caching and coordination to prevent duplicate API calls when
    multiple requests for the same state happen concurrently. Each request
    fetches exactly 1 city, and concurrent requests coordinate to fetch
    different cities.
    """
    state_name = _get_state_name(state_code)
    total_available_cities = _get_total_available_cities(state_code)

    # Coordinate to pick a city that's not cached and not being fetched
    city_to_fetch = None
    future = None

    async with _in_flight_lock:
        # Check cache after acquiring lock
        cities = _city_cache.get(state_code, {})

        # Fast path: if cache is fully populated, just return a random city
        if cities and len(cities) >= total_available_cities:
            return random.choice(list(cities.values()))

        # Get all available cities and find one that's not cached and not in-flight
        all_available_cities = MAJOR_CITIES.get(state_code, [])
        if not all_available_cities:
            # Fallback: use state name
            city_to_fetch = state_name if state_code != "DC" else "Washington"
        else:
            in_flight_cities = _in_flight_cities.get(state_code, set())
            available_to_fetch = [
                city
                for city in all_available_cities
                if city not in cities and city not in in_flight_cities
            ]
            if available_to_fetch:
                # Fetch a new city
                city_to_fetch = random.choice(available_to_fetch)
            elif cities:
                # All uncached cities are in-flight, use a cached one
                return random.choice(list(cities.values()))
            else:
                # No cities cached and all are in-flight
                # Will wait and retry after releasing lock
                city_to_fetch = None

        # Mark this city as in-flight (if we have one to fetch)
        if city_to_fetch is not None:
            if state_code not in _in_flight_cities:
                _in_flight_cities[state_code] = set()
            _in_flight_cities[state_code].add(city_to_fetch)

            # Create a future for this specific city fetch
            loop = asyncio.get_running_loop()
            future = loop.create_future()

            # Start the fetch task
            asyncio.create_task(
                _fetch_and_set_result(
                    state_code,
                    state_name,
                    city_to_fetch,
                    future,
                    rate_limiter,
                )
            )

    # If all cities are in-flight and none are cached, wait and retry
    if city_to_fetch is None:
        await asyncio.sleep(0.2)
        return await get_random_city_bbox_async(state_code, rate_limiter)

    # Wait for the fetch to complete
    # Note: await future already yields to the event loop when the future isn't ready
    try:
        await future
        # Pick from cache (which now includes the newly fetched city)
        async with _in_flight_lock:
            cities = _city_cache.get(state_code, {})
            if cities:
                return random.choice(list(cities.values()))
            raise Exception("Cache was not populated after fetch completed")
    except Exception:
        # If fetch failed, remove from in-flight and try cache
        async with _in_flight_lock:
            if city_to_fetch is not None and state_code in _in_flight_cities:
                _in_flight_cities[state_code].discard(city_to_fetch)
            cities = _city_cache.get(state_code, {})
            if cities:
                return random.choice(list(cities.values()))
        raise


async def _fetch_and_set_result(
    state_code: str,
    state_name: str,
    city_to_fetch: str,
    future: asyncio.Future[Any],
    rate_limiter: RateLimiter,
) -> None:
    """Fetch a specific city for a state and populate cache, then signal completion.

    The future is used as a signal that the cache has been populated,
    not to return a specific bounding box. Each caller will pick randomly
    from the cache after the future completes.
    """
    try:
        await _fetch_city_bbox_async(
            state_code,
            state_name,
            rate_limiter,
            city_to_fetch,
        )
        async with _in_flight_lock:
            # Remove this city from in-flight set
            if state_code in _in_flight_cities:
                _in_flight_cities[state_code].discard(city_to_fetch)
            if not future.done():
                future.set_result(None)
    except Exception as e:
        async with _in_flight_lock:
            # Remove this city from in-flight set even on error
            if state_code in _in_flight_cities:
                _in_flight_cities[state_code].discard(city_to_fetch)
            if not future.done():
                future.set_exception(e)


def _extract_street_address(addr_parts: Dict[str, Any]) -> Optional[str]:
    """Extract and validate street address from address parts."""
    house_num = addr_parts.get("house_number")
    road = (
        addr_parts.get("road")
        or addr_parts.get("street")
        or addr_parts.get("pedestrian")
        or addr_parts.get("residential")
    )

    # Require at least a road/street name
    if not road:
        return None

    # If we have a house number, use it; otherwise just use the road
    street = f"{house_num} {road}" if house_num else road

    # Reject addresses with semicolons (usually indicates multiple highways)
    if ";" in street:
        return None

    # Reject addresses that look like highway/interstate designations only
    # Pattern: starts with I, US, SR, or similar followed by numbers, and that's it
    street_upper = street.upper().strip()
    # Check for patterns like "I 76", "I-76", "US 77", "SR 123", etc.
    # Must be ONLY the highway designation (no additional street name)
    # This matches: "I 76", "I-76", "US 77", but NOT "I 76 Main Street"
    highway_pattern = r"^(I|US|SR|STATE\s*ROUTE|HIGHWAY|HWY|RT|ROUTE)[\s-]*\d+\s*$"
    if re.match(highway_pattern, street_upper):
        # Only reject if it's JUST a highway designation (no house number or other text)
        # Allow if there's a house number (e.g., "123 I-76" is valid)
        if not house_num or house_num.strip() == "":
            return None

    # Require either a house number OR a digit in the street name
    # This allows addresses like "123 Main St" or "Route 1" or "Highway 2"
    # but rejects addresses with no numbers at all (which are less reliable)
    has_house_number = house_num is not None and house_num.strip() != ""
    has_digit_in_street = any(c.isdigit() for c in street)
    if not (has_house_number or has_digit_in_street):
        return None

    return street


def _normalize_state_code(state_name: str) -> str:
    """Convert state name to 2-letter abbreviation."""
    try:
        state_obj = us.states.lookup(state_name)
        if state_obj:
            return state_obj.abbr
    except Exception:
        pass

    # Fallback: use state_name as-is if it's already 2 letters
    return state_name if len(state_name) == 2 else state_name


def _normalize_postal_code(postal: str) -> str:
    """Validate and normalize postal code format."""
    if not postal:
        return ""

    postal_clean = postal.replace("-", "").replace(" ", "")
    if postal_clean.isdigit() and len(postal_clean) >= 5:
        return postal

    return ""


def _parse_address(location: Location) -> Optional[str]:
    """Parse address from location object."""
    if not location or not location.address:
        return None

    if not (hasattr(location, "raw") and "address" in location.raw):  # type: ignore
        return None

    addr_parts = location.raw["address"]  # type: ignore

    # Extract and validate street address
    street = _extract_street_address(addr_parts)
    if not street:
        return None

    # Extract city and state
    city = addr_parts.get("city", addr_parts.get("town", addr_parts.get("village", "")))
    state_name = addr_parts.get("state", "")

    # Require both city and state for a complete US address
    if not city or not state_name:
        return None

    # Normalize state code
    state_abbr = _normalize_state_code(state_name)

    # Normalize postal code
    postal_raw = addr_parts.get("postcode", "")
    postal = _normalize_postal_code(postal_raw)

    # Format: street on line 1, city on line 2, state + zip on line 3
    lines = [street, city]
    state_zip = state_abbr
    if postal:
        state_zip += f" {postal}"
    lines.append(state_zip)

    return "\n".join(lines)


async def _cancel_remaining_tasks(tasks: List[asyncio.Task]) -> None:
    """Cancel remaining tasks and handle cancellation gracefully."""
    remaining = [t for t in tasks if not t.done()]
    if not remaining:
        return

    for task in remaining:
        task.cancel()

    # Briefly await cancelled tasks to handle cancellation exceptions
    # This prevents "task was destroyed but is pending" warnings
    try:
        await asyncio.wait_for(
            asyncio.gather(*remaining, return_exceptions=True),
            timeout=0.05,  # Very short timeout - don't block
        )
    except asyncio.TimeoutError:
        # Tasks still running in thread pool, proceed anyway
        pass


async def _get_address_async(
    state_code: str,
    rate_limiter: RateLimiter,
) -> str:
    """Async function to get a real address by trying multiple locations in parallel."""
    # Try multiple cities if one doesn't yield an address
    for city_attempt in range(_MAX_CITIES_TO_TRY):
        # Get a random city's bounding box (this may be cached, so it's fast)
        min_lat, max_lat, min_lon, max_lon = await get_random_city_bbox_async(
            state_code, rate_limiter
        )

        # Try multiple locations in parallel (batch size for concurrency)
        for batch in range(_MAX_ADDRESS_BATCHES):
            # Generate random coordinates for this batch
            tasks = []
            for _ in range(_ADDRESS_BATCH_SIZE):
                lat = random.uniform(min_lat, max_lat)
                lon = random.uniform(min_lon, max_lon)
                tasks.append(
                    asyncio.create_task(_reverse_geocode_async(lat, lon, rate_limiter))
                )

            # Check results as they complete - return immediately on first success
            for coro in asyncio.as_completed(tasks):
                try:
                    location = await coro
                except asyncio.CancelledError:
                    continue
                except Exception:
                    continue

                if not location:
                    continue

                address = _parse_address(location)
                if address:
                    _api_stats["reverse_geocoding_successes"] += 1
                    # Cancel remaining tasks in this batch to avoid unnecessary API calls
                    await _cancel_remaining_tasks(tasks)
                    return address

        # If we get here, this city didn't yield an address
        # Try a different city on the next iteration

    raise ValueError(
        f"Could not find a valid address after trying {_MAX_CITIES_TO_TRY} cities "
        f"with {_MAX_ADDRESS_BATCHES} batches each"
    )


async def get_real_address_async(
    state_code: str,
    rate_limiter: RateLimiter,
) -> str:
    """Get a real address by reverse geocoding random coordinates in cities (async)."""
    return await _get_address_async(state_code, rate_limiter)


def _validate_state_code(state_code: str) -> None:
    """Validate state code and exit if invalid."""
    if state_code == "DC":
        return
    try:
        state = us.states.lookup(state_code)
        if not state:
            raise ValueError("Invalid state code")
    except Exception:
        msg = (
            f"Error: Invalid state code '{state_code}'. "
            "Use a valid 2-letter US state code."
        )
        print(msg, file=sys.stderr)
        sys.exit(1)


def _generate_fake_data(fake: Faker) -> Dict[str, Any]:
    """Generate synthetic test data (name, email, dob)."""
    dob = fake.date_of_birth(minimum_age=_AGE_RANGE[0], maximum_age=_AGE_RANGE[1])
    return {
        "name": fake.name(),
        "email": f"@{fake.word()}{fake.random_int(min=1, max=999)}",
        "dob": f"{dob.month:02}/{dob.day:02}/{dob.year}",
    }


async def _generate_record_async(
    state_code: str,
    rate_limiter: RateLimiter,
    fake: Faker,
) -> Dict[str, Any]:
    """Generate a single record asynchronously."""
    fake_data = _generate_fake_data(fake)
    try:
        real_address = await get_real_address_async(state_code, rate_limiter)
        return {
            **fake_data,
            "address": real_address,
            "error": None,
        }
    except Exception as e:
        return {
            **fake_data,
            "address": None,
            "error": str(e),
        }


def _print_record(result: Dict[str, Any], record_num: int) -> None:
    """Print a single record with the given record number."""
    print("—" * 15, f"{record_num:02}", "—" * 15)
    print(f"\n{result['name']}")
    print(result["email"])
    print(f"{result['dob']}\n")
    if result.get("error"):
        print(f"Error: {result['error']}\n")
    else:
        print(f"{result['address']}\n")


async def _generate_all_records_async(
    num_records: int,
    state_code: Optional[str],
    rate_limiter: RateLimiter,
    fake: Faker,
) -> None:
    """Generate all records in parallel, printing as they complete."""
    tasks = []
    for _ in range(num_records):
        # If no state specified, randomly select one
        if state_code is None:
            available_states = list(MAJOR_CITIES.keys())
            selected_state = random.choice(available_states)
        else:
            selected_state = state_code.upper()
            _validate_state_code(selected_state)

        tasks.append(_generate_record_async(selected_state, rate_limiter, fake))

    # Counter for assigning record numbers as they're printed
    print_counter = 0
    print_lock = asyncio.Lock()

    async def _print_when_done(task: asyncio.Task) -> Any:
        nonlocal print_counter
        result = await task
        if isinstance(result, Exception):
            print(f"Error: {result}", file=sys.stderr)
            return result
        if isinstance(result, dict):
            # Assign number dynamically as we print
            async with print_lock:
                print_counter += 1
                record_num = print_counter
            _print_record(result, record_num)
            # Track successful records (those with addresses, no errors)
            if not result.get("error") and result.get("address"):
                _api_stats["successful_records"] += 1
        return result

    # Use as_completed to process results as they finish
    tasks_with_print = [_print_when_done(task) for task in tasks]
    await asyncio.gather(*tasks_with_print, return_exceptions=True)


def main() -> None:
    """Main entry point."""
    desc = "Generate synthetic test data with real US addresses for testing and research"
    parser = argparse.ArgumentParser(description=desc)
    parser.add_argument(
        "num",
        type=int,
        nargs="?",
        default=_DEFAULT_NUM_RECORDS,
        help=f"Number of records to generate (default: {_DEFAULT_NUM_RECORDS})",
    )
    parser.add_argument(
        "state",
        type=str,
        nargs="?",
        default=None,
        help=(
            "US state code (e.g., CA, NY, TX). "
            "If not provided, randomly selects a state."
        ),
    )
    parser.add_argument(
        "--debug",
        action="store_true",
        help="Print debug messages and API call summary",
    )

    args = parser.parse_args()

    if args.num <= 0:
        print("Error: Number must be positive", file=sys.stderr)
        sys.exit(1)

    # Set debug mode globally
    global _debug_mode
    _debug_mode = args.debug

    # Reset API call counters
    for key in _api_stats:
        _api_stats[key] = 0

    fake = Faker("en_US")

    # Unified rate limiter for all geocoding requests (city + address lookups)
    # This prevents overwhelming the Nominatim API with too many concurrent requests
    # The geolocator is now managed internally by the rate limiter using AioHTTPAdapter
    rate_limiter = RateLimiter(
        _MAX_CONCURRENT_CITY_FETCHES, _MAX_CONCURRENT_REVERSE_GEOCODE
    )

    # Generate all records in parallel, printing as they complete
    async def _run_and_cleanup():
        try:
            await _generate_all_records_async(args.num, args.state, rate_limiter, fake)
        finally:
            # Stop queue worker by sending sentinel
            global _api_queue, _api_queue_worker
            if _api_queue is not None and _api_queue_worker is not None:
                # Wait for queue to be empty (all tasks processed)
                await _api_queue.join()
                # Send sentinel to stop worker
                await _api_queue.put(None)
                # Wait for worker to finish processing sentinel
                try:
                    await asyncio.wait_for(_api_queue_worker, timeout=2.0)
                except asyncio.TimeoutError:
                    # Worker didn't stop in time, cancel it
                    _api_queue_worker.cancel()
                    try:
                        await _api_queue_worker
                    except asyncio.CancelledError:
                        pass
                _api_queue_worker = None
                _api_queue = None

            # Clean up async geolocator
            global _geolocator
            if _geolocator is not None:
                try:
                    await _geolocator.__aexit__(None, None, None)
                except Exception:
                    pass  # Ignore errors during cleanup
                _geolocator = None

    asyncio.run(_run_and_cleanup())

    # Print API call summary if debug mode is enabled
    if _debug_mode:
        print("\n" + "=" * 60, file=sys.stderr)
        print("API CALL SUMMARY", file=sys.stderr)
        print("=" * 60, file=sys.stderr)
        geocoding_calls = _api_stats["geocoding_calls"]
        geocoding_successes = _api_stats["geocoding_successes"]
        geocoding_pct = (
            100 * geocoding_successes / geocoding_calls if geocoding_calls > 0 else 0.0
        )
        print(
            (
                f"Geocoding:     {geocoding_successes}/{geocoding_calls} successful "
                f"({geocoding_pct:.1f}%)"
                if geocoding_calls > 0
                else "Geocoding:     0/0 (no calls)"
            ),
            file=sys.stderr,
        )
        reverse_calls = _api_stats["reverse_geocoding_calls"]
        reverse_successes = _api_stats["reverse_geocoding_successes"]
        reverse_pct = (
            100 * reverse_successes / reverse_calls if reverse_calls > 0 else 0.0
        )
        print(
            (
                f"Reverse geocoding: {reverse_successes}/{reverse_calls} addresses used "
                f"({reverse_pct:.1f}%)"
                if reverse_calls > 0
                else "Reverse geocoding: 0/0 (no calls)"
            ),
            file=sys.stderr,
        )
        total_calls = geocoding_calls + reverse_calls
        total_failed_calls = (
            _api_stats["geocoding_failures"] + _api_stats["reverse_geocoding_failures"]
        )
        failed_api_pct = (
            100 * total_failed_calls / total_calls if total_calls > 0 else 0.0
        )
        # Geocoding calls needed: only count actual API calls (cached cities don't count)
        # Reverse geocoding calls needed: 1 per successful record
        # (reverse_successes equals _api_stats["successful_records"])
        total_needed = geocoding_calls + reverse_successes
        print(
            f"\nTotal API calls made: {total_calls} " f"({failed_api_pct:.1f}% failed)",
            file=sys.stderr,
        )
        print(
            f"API calls actually needed: {total_needed} "
            f"({geocoding_calls} geocoding + {reverse_successes} reverse)",
            file=sys.stderr,
        )
        successful_records = _api_stats["successful_records"]
        failed_records = args.num - successful_records
        failed_pct = 100 * failed_records / args.num if args.num > 0 else 0.0
        print(
            f"Records: {successful_records}/{args.num} successful "
            f"({failed_pct:.1f}% failed)",
            file=sys.stderr,
        )
        if total_calls > 0:
            efficiency = 100 * total_needed / total_calls
            wasted = total_calls - total_needed
            print(
                f"Efficiency: {efficiency:.1f}% "
                f"({total_needed}/{total_calls} calls were necessary)",
                file=sys.stderr,
            )
            if wasted > 0:
                unused_reverse = (
                    _api_stats["reverse_geocoding_calls"]
                    - _api_stats["reverse_geocoding_successes"]
                    - _api_stats["reverse_geocoding_failures"]
                )
                print(
                    f"Wasted calls: {wasted} "
                    f"({unused_reverse} unused reverse geocoding attempts)",
                    file=sys.stderr,
                )
        print("=" * 60 + "\n", file=sys.stderr)


if __name__ == "__main__":
    main()
