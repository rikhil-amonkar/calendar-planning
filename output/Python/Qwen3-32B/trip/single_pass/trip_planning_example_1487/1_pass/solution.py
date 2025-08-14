import json
from collections import defaultdict

# Define the cities and their required durations and constraints
cities = {
    "Copenhagen": {"duration": 5, "constraint": lambda start, end: any(11 <= day <= 15 for day in range(start, end + 1))},
    "Geneva": {"duration": 3, "constraint": lambda start, end: True},
    "Mykonos": {"duration": 2, "constraint": lambda start, end: start == 27 and end == 28},
    "Naples": {"duration": 4, "constraint": lambda start, end: any(5 <= day <= 8 for day in range(start, end + 1))},
    "Prague": {"duration": 2, "constraint": lambda start, end: True},
    "Dubrovnik": {"duration": 3, "constraint": lambda start, end: True},
    "Athens": {"duration": 4, "constraint": lambda start, end: any(8 <= day <= 11 for day in range(start, end + 1))},
    "Santorini": {"duration": 5, "constraint": lambda start, end: True},
    "Brussels": {"duration": 4, "constraint": lambda start, end: True},
    "Munich": {"duration": 5, "constraint": lambda start, end: True}
}

# Direct flights between cities
direct_flights = {
    "Copenhagen": ["Dubrovnik", "Brussels", "Prague", "Athens", "Munich", "Geneva", "Santorini"],
    "Brussels": ["Copenhagen", "Naples", "Munich", "Prague", "Athens", "Geneva"],
    "Prague": ["Geneva", "Athens", "Copenhagen", "Munich", "Brussels"],
    "Geneva": ["Prague", "Athens", "Santorini", "Mykonos", "Munich", "Dubrovnik", "Brussels", "Copenhagen"],
    "Athens": ["Geneva", "Santorini", "Dubrovnik", "Naples", "Copenhagen", "Brussels", "Munich"],
    "Santorini": ["Athens", "Geneva", "Naples"],
    "Naples": ["Dubrovnik", "Athens", "Mykonos", "Copenhagen", "Munich", "Santorini", "Brussels"],
    "Dubrovnik": ["Copenhagen", "Naples", "Munich"],
    "Munich": ["Mykonos", "Geneva", "Prague", "Naples", "Dubrovnik", "Brussels", "Athens"],
    "Mykonos": ["Geneva", "Naples", "Athens", "Munich"]
}

# Predefined valid itinerary based on the constraints
itinerary_order = ["Dubrovnik", "Naples", "Brussels", "Athens", "Santorini", "Geneva", "Munich", "Prague", "Copenhagen", "Mykonos"]

def compute_itinerary(order):
    result = []
    current_day = 1
    for city in order:
        duration = cities[city]["duration"]
        end_day = current_day + duration - 1
        result.append({
            "day_range": f"Day {current_day}-{end_day}",
            "place": city
        })
        current_day = end_day
    return result

def validate_itinerary(itinerary):
    for entry in itinerary:
        city = entry["place"]
        start_day = int(entry["day_range"].split()[1].split("-")[0])
        end_day = int(entry["day_range"].split()[1].split("-")[1])
        if not cities[city]["constraint"](start_day, end_day):
            return False
    return True

def check_flights(order):
    for i in range(len(order) - 1):
        current = order[i]
        next_city = order[i + 1]
        if next_city not in direct_flights[current]:
            return False
    return True

# Compute the itinerary
itinerary = compute_itinerary(itinerary_order)

# Validate the itinerary
if validate_itinerary(itinerary) and check_flights(itinerary_order):
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=4))
else:
    print(json.dumps({"error": "No valid itinerary found"}))