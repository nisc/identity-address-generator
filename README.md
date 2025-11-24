# Identity Address Generator

A testing and research tool for generating synthetic test data with real US addresses. Useful for software testing, data anonymization research, and development workflows that require realistic address data.

## Usage

```bash
python -m venv venv
source venv/bin/activate  # On Windows: venv\Scripts\activate
pip install -r requirements.txt
python generate.py [--debug] [num_identities] [US state]
```

- `--debug`: Show API call statistics (optional, can be placed anywhere)
- `num_identities`: Number of test records to generate (default: 3)
- `US state`: State code (e.g., CA, NY, TX). If omitted, randomly selects a state.

## Approach

The tool selects random coordinates within major US cities and uses reverse geocoding to retrieve real addresses from the Nominatim API. City boundaries are cached to minimize API calls. Throttling is applied
to stay within free usage limits and avoid API bans.
