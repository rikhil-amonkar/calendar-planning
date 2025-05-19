import json
from datetime import datetime, timedelta

def main():
    itinerary = [
        {"day_range": "Day 1-5", "place": "Valencia"},
        {"day_range": "Day 5-6", "place": "Barcelona"},
        {"day_range": "Day 6-10", "place": "Venice"},
        {"day_range": "Day 10-14", "place": "Amsterdam"},
        {"day_range": "Day 14-19", "place": "Split"},
        {"day_range": "Day 19-21", "place": "Stuttgart"},
        {"day_range": "Day 21-24", "place": "Naples"},
        {"day_range": "Day 24-24", "place": "Nice"}
    ]

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()