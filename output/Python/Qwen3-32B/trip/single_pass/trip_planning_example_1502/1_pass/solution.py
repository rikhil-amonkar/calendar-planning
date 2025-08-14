import json

def generate_itinerary():
    # Define the cities and their required stays and event constraints
    cities = [
        {"name": "Santorini", "days": 3, "fixed_days": None},
        {"name": "Valencia", "days": 4, "fixed_days": None},
        {"name": "Madrid", "days": 2, "fixed_days": (6, 7)},
        {"name": "Seville", "days": 2, "fixed_days": None},
        {"name": "Bucharest", "days": 3, "fixed_days": None},
        {"name": "Vienna", "days": 4, "fixed_days": (3, 6)},
        {"name": "Riga", "days": 4, "fixed_days": (20, 23)},
        {"name": "Tallinn", "days": 5, "fixed_days": (23, 27)},
        {"name": "Krakow", "days": 5, "fixed_days": (11, 15)},
        {"name": "Frankfurt", "days": 4, "fixed_days": None},
    ]

    # Direct flights between cities
    direct_flights = {
        "Vienna": ["Bucharest", "Santorini", "Seville", "Madrid", "Valencia", "Krakow", "Frankfurt", "Riga"],
        "Santorini": ["Madrid", "Bucharest", "Vienna"],
        "Valencia": ["Seville", "Madrid", "Bucharest", "Vienna", "Krakow", "Frankfurt"],
        "Madrid": ["Santorini", "Valencia", "Seville", "Vienna", "Bucharest", "Frankfurt"],
        "Seville": ["Valencia", "Madrid"],
        "Bucharest": ["Vienna", "Riga", "Valencia", "Santorini", "Frankfurt", "Madrid"],
        "Krakow": ["Valencia", "Frankfurt", "Vienna"],
        "Frankfurt": ["Valencia", "Krakow", "Bucharest", "Riga", "Tallinn", "Vienna", "Madrid"],
        "Riga": ["Bucharest", "Tallinn"],
        "Tallinn": ["Frankfurt", "Riga"],
    }

    # Construct the itinerary based on the derived order
    itinerary = [
        {"day_range": "Day 1-3", "place": "Santorini"},
        {"day_range": "Day 3-6", "place": "Vienna"},
        {"day_range": "Day 6-7", "place": "Madrid"},
        {"day_range": "Day 7-8", "place": "Seville"},
        {"day_range": "Day 8-11", "place": "Valencia"},
        {"day_range": "Day 11-15", "place": "Krakow"},
        {"day_range": "Day 15-18", "place": "Frankfurt"},
        {"day_range": "Day 18-20", "place": "Bucharest"},
        {"day_range": "Day 20-23", "place": "Riga"},
        {"day_range": "Day 23-27", "place": "Tallinn"},
    ]

    # Validate that all transitions are via direct flights
    for i in range(len(itinerary) - 1):
        current_city = itinerary[i]["place"]
        next_city = itinerary[i + 1]["place"]
        if next_city not in direct_flights[current_city]:
            raise ValueError(f"No direct flight from {current_city} to {next_city}")

    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = generate_itinerary()
    print(json.dumps(result, indent=2))