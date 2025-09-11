import json

# Define cities and their required stay durations and constraints
cities = {
    "Edinburgh": {"days": 5, "constraints": [{"type": "in_range", "days": [1, 5]}]},
    "Budapest": {"days": 5, "constraints": [{"type": "in_range", "days": [9, 13]}]},
    "Warsaw": {"days": 5, "constraints": [{"type": "on_days", "days": [25, 29]}]},
    "Munich": {"days": 3, "constraints": [{"type": "in_range", "days": [18, 20]}]},
    "Stockholm": {"days": 2, "constraints": [{"type": "in_range", "days": [17, 18]}]},
    "Riga": {"days": 5},
    "Bucharest": {"days": 2},
    "Krakow": {"days": 4},
    "Barcelona": {"days": 5},
    "Vienna": {"days": 5}
}

# Define direct flights as adjacency list
direct_flights = {
    "Budapest": ["Munich", "Vienna", "Bucharest", "Warsaw", "Barcelona"],
    "Bucharest": ["Riga", "Munich", "Budapest", "Barcelona"],
    "Munich": ["Krakow", "Warsaw", "Bucharest", "Budapest", "Barcelona", "Stockholm", "Edinburgh", "Vienna"],
    "Krakow": ["Munich", "Warsaw", "Barcelona", "Stockholm", "Edinburgh"],
    "Warsaw": ["Munich", "Barcelona", "Stockholm", "Krakow", "Vienna"],
    "Barcelona": ["Warsaw", "Munich", "Budapest", "Riga", "Krakow", "Edinburgh", "Stockholm", "Vienna"],
    "Edinburgh": ["Stockholm", "Krakow", "Munich", "Budapest", "Riga", "Barcelona"],
    "Stockholm": ["Edinburgh", "Krakow", "Riga", "Warsaw", "Barcelona"],
    "Riga": ["Bucharest", "Munich", "Stockholm", "Warsaw"],
    "Vienna": ["Budapest", "Warsaw", "Munich", "Barcelona", "Bucharest", "Riga"]
}

# Define the revised itinerary order
itinerary_order = [
    "Edinburgh", "Riga", "Bucharest", "Budapest", "Munich", "Stockholm", "Krakow", "Munich", "Vienna", "Warsaw", "Barcelona", "Vienna"
]

# Calculate day ranges and adjust for direct flights
def calculate_day_ranges(itinerary_order, cities, direct_flights):
    current_day = 1
    itinerary = []
    for i, city in enumerate(itinerary_order):
        stay_days = cities[city]["days"]
        end_day = current_day + stay_days - 1
        itinerary.append({"city": city, "start": current_day, "end": end_day})
        current_day = end_day + 1  # Next city starts the next day (no overlap)

    # Adjust for overlapping days when flights are taken
    for i in range(1, len(itinerary)):
        prev_city = itinerary[i-1]["city"]
        current_city = itinerary[i]["city"]
        if current_city in direct_flights[prev_city]:
            itinerary[i]["start"] -= 1
        else:
            raise ValueError(f"No direct flight from {prev_city} to {current_city}")
    
    return itinerary

# Validate constraints
def validate_constraints(itinerary, cities):
    for entry in itinerary:
        city = entry["city"]
        start = entry["start"]
        end = entry["end"]
        for constraint in cities[city]["constraints"]:
            if constraint["type"] == "in_range":
                if not (start <= constraint["days"][1] and end >= constraint["days"][0]):
                    return False
            elif constraint["type"] == "on_days":
                if not (start <= constraint["days"][0] and end >= constraint["days"][1]):
                    return False
    return True

# Generate the itinerary
try:
    itinerary = calculate_day_ranges(itinerary_order, cities, direct_flights)
    if validate_constraints(itinerary, cities):
        # Format the itinerary for output
        formatted_itinerary = []
        for entry in itinerary:
            formatted_itinerary.append({
                "day_range": f"Day {entry['start']}-{entry['end']}",
                "place": entry["city"]
            })
        output = {"itinerary": formatted_itinerary}
        print(json.dumps(output, indent=2))
    else:
        print("Failed to satisfy all constraints.")
except ValueError as e:
    print(f"Invalid itinerary: {e}")