import json

def main():
    # Define cities in the correct sequence
    cities = [
        {"name": "Vienna", "duration": 2},
        {"name": "Helsinki", "duration": 3},
        {"name": "Riga", "duration": 3},
        {"name": "Tallinn", "duration": 5},
        {"name": "Dublin", "duration": 5},
        {"name": "Reykjavik", "duration": 2},
    ]

    # Define direct flights as a set of frozensets
    direct_flights = {
        frozenset({"Helsinki", "Riga"}),
        frozenset({"Riga", "Tallinn"}),
        frozenset({"Vienna", "Helsinki"}),
        frozenset({"Riga", "Dublin"}),
        frozenset({"Vienna", "Riga"}),
        frozenset({"Reykjavik", "Vienna"}),
        frozenset({"Helsinki", "Dublin"}),
        frozenset({"Tallinn", "Dublin"}),
        frozenset({"Reykjavik", "Dublin"}),
        frozenset({"Helsinki", "Tallinn"}),
        frozenset({"Vienna", "Dublin"}),
    }

    # Validate consecutive cities have direct flights
    for i in range(len(cities) - 1):
        city1 = cities[i]["name"]
        city2 = cities[i + 1]["name"]
        if frozenset({city1, city2}) not in direct_flights:
            raise ValueError(f"No direct flight between {city1} and {city2}")

    # Calculate day ranges
    itinerary = []
    start_day = 1
    for city in cities:
        end_day = start_day + city["duration"] - 1
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city["name"]})
        start_day = end_day  # Next city starts on this day

    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()