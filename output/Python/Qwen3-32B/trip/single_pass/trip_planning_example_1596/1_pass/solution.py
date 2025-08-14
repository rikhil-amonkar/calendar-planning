import json

# Define the cities and their required durations and constraints
cities = {
    "Edinburgh": {"duration": 5, "constraint": {"type": "range", "days": [1, 5]}},
    "Riga": {"duration": 5, "constraint": {"type": "none"}},
    "Budapest": {"duration": 5, "constraint": {"type": "range", "days": [9, 13]}},
    "Vienna": {"duration": 5, "constraint": {"type": "none"}},
    "Stockholm": {"duration": 2, "constraint": {"type": "range", "days": [17, 18]}},
    "Munich": {"duration": 3, "constraint": {"type": "range", "days": [18, 20]}},
    "Krakow": {"duration": 4, "constraint": {"type": "none"}},
    "Warsaw": {"duration": 5, "constraint": {"type": "range", "days": [25, 29]}},
    "Bucharest": {"duration": 2, "constraint": {"type": "none"}},
    "Barcelona": {"duration": 5, "constraint": {"type": "none"}},
}

# Define direct flights between cities
direct_flights = {
    ("Edinburgh", "Riga"),
    ("Riga", "Budapest"),
    ("Budapest", "Vienna"),
    ("Vienna", "Stockholm"),
    ("Stockholm", "Munich"),
    ("Munich", "Krakow"),
    ("Krakow", "Warsaw"),
    ("Warsaw", "Bucharest"),
    ("Bucharest", "Barcelona"),
    # Add reverse flights for completeness
    ("Riga", "Edinburgh"),
    ("Budapest", "Riga"),
    ("Vienna", "Budapest"),
    ("Stockholm", "Vienna"),
    ("Munich", "Stockholm"),
    ("Krakow", "Munich"),
    ("Warsaw", "Krakow"),
    ("Bucharest", "Warsaw"),
    ("Barcelona", "Bucharest"),
}

# Define the order of cities in the itinerary
itinerary_order = [
    "Edinburgh",
    "Riga",
    "Budapest",
    "Vienna",
    "Stockholm",
    "Munich",
    "Krakow",
    "Warsaw",
    "Bucharest",
    "Barcelona",
]

# Calculate day ranges for each city
itinerary = []
current_day = 1

for city in itinerary_order:
    duration = cities[city]["duration"]
    end_day = current_day + duration - 1
    if cities[city]["constraint"]["type"] == "range":
        # Ensure the constraint is satisfied
        constraint_start, constraint_end = cities[city]["constraint"]["days"]
        if not (current_day <= constraint_end and end_day >= constraint_start):
            raise ValueError(f"Constraint not satisfied for {city}")
    itinerary.append({
        "day_range": f"Day {current_day}-{end_day}",
        "place": city
    })
    # Update current_day for next city (flight day is counted in both cities)
    current_day = end_day + 1

# Output the JSON
json_output = {"itinerary": itinerary}
print(json.dumps(json_output, indent=2))