import json

def main():
    # Define cities and their required durations
    cities = {
        "Prague": 5,
        "Tallinn": 3,
        "Warsaw": 2,
        "Porto": 3,
        "Naples": 5,
        "Milan": 3,
        "Lisbon": 5,
        "Santorini": 5,
        "Riga": 4,
        "Stockholm": 2
    }

    # Fixed constraints for specific cities
    fixed = {
        "Riga": {"start": 5, "end": 8},
        "Tallinn": {"start": 18, "end": 20},
        "Milan": {"start": 24, "end": 26}
    }

    # Define direct flights as a graph (adjacency list)
    direct_flights = {
        "Prague": ["Riga", "Tallinn", "Warsaw", "Lisbon", "Milan", "Stockholm"],
        "Tallinn": ["Riga", "Prague", "Warsaw", "Stockholm"],
        "Warsaw": ["Naples", "Lisbon", "Milan", "Porto", "Tallinn", "Riga", "Stockholm"],
        "Porto": ["Lisbon", "Milan", "Warsaw"],
        "Naples": ["Warsaw", "Milan", "Lisbon", "Santorini"],
        "Milan": ["Stockholm", "Porto", "Naples", "Santorini", "Stockholm", "Warsaw"],
        "Lisbon": ["Stockholm", "Riga", "Naples", "Porto", "Prague", "Warsaw"],
        "Santorini": ["Milan", "Naples"],
        "Riga": ["Prague", "Tallinn", "Milan", "Lisbon", "Stockholm", "Warsaw"],
        "Stockholm": ["Milan", "Lisbon", "Riga", "Tallinn", "Warsaw"]
    }

    # Construct the itinerary based on constraints and direct flights
    itinerary = [
        {"day_range": "Day 1-5", "place": "Prague"},
        {"day_range": "Day 5-8", "place": "Riga"},
        {"day_range": "Day 8-9", "place": "Stockholm"},
        {"day_range": "Day 9-13", "place": "Lisbon"},
        {"day_range": "Day 13-17", "place": "Naples"},
        {"day_range": "Day 17-18", "place": "Warsaw"},
        {"day_range": "Day 18-20", "place": "Tallinn"},
        {"day_range": "Day 20-24", "place": "Santorini"},
        {"day_range": "Day 24-26", "place": "Milan"},
        {"day_range": "Day 26-28", "place": "Porto"}
    ]

    # Verify direct flights between consecutive cities in the itinerary
    for i in range(len(itinerary) - 1):
        current = itinerary[i]["place"]
        next_city = itinerary[i + 1]["place"]
        if next_city not in direct_flights[current]:
            raise ValueError(f"No direct flight from {current} to {next_city}")

    # Output the result as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()