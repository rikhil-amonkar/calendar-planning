import json

def main():
    # Define cities and their required durations
    cities = {
        "Riga": 2,
        "Frankfurt": 3,
        "Amsterdam": 2,
        "Vilnius": 5,
        "London": 2,
        "Stockholm": 3,
        "Bucharest": 4
    }

    # Direct flights (bidirectional)
    direct_flights = {
        ("London", "Amsterdam"), ("Vilnius", "Frankfurt"), ("Riga", "Vilnius"),
        ("Riga", "Stockholm"), ("London", "Bucharest"), ("Amsterdam", "Stockholm"),
        ("Amsterdam", "Frankfurt"), ("Frankfurt", "Stockholm"), ("Bucharest", "Riga"),
        ("Amsterdam", "Riga"), ("Amsterdam", "Bucharest"), ("Riga", "Frankfurt"),
        ("Bucharest", "Frankfurt"), ("London", "Frankfurt"), ("London", "Stockholm"),
        ("Amsterdam", "Vilnius")
    }

    # Add reverse flights for bidirectional connections
    bidirectional_flights = set()
    for a, b in direct_flights:
        bidirectional_flights.add((a, b))
        bidirectional_flights.add((b, a))

    # Construct the itinerary based on constraints
    itinerary = [
        {"day_range": "Day 1-2", "place": "London"},
        {"day_range": "Day 2-3", "place": "Amsterdam"},
        {"day_range": "Day 3-6", "place": "Bucharest"},
        {"day_range": "Day 6-7", "place": "Riga"},
        {"day_range": "Day 7-11", "place": "Vilnius"},
        {"day_range": "Day 11-13", "place": "Frankfurt"},
        {"day_range": "Day 13-15", "place": "Stockholm"}
    ]

    # Verify transitions between cities
    for i in range(len(itinerary) - 1):
        current_city = itinerary[i]["place"]
        next_city = itinerary[i + 1]["place"]
        if (current_city, next_city) not in bidirectional_flights:
            raise ValueError(f"No direct flight from {current_city} to {next_city}")

    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()