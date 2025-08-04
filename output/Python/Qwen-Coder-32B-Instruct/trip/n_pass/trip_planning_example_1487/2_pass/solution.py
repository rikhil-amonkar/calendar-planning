import json
from itertools import permutations

# Define the constraints
cities = {
    "Copenhagen": {"days": 5, "must_visit": (11, 15)},
    "Geneva": {"days": 3},
    "Mykonos": {"days": 2, "must_visit": (27, 28)},
    "Naples": {"days": 4, "must_visit": (5, 8)},
    "Prague": {"days": 2},
    "Dubrovnik": {"days": 3},
    "Athens": {"days": 4, "must_visit": (8, 11)},
    "Santorini": {"days": 5},
    "Brussels": {"days": 4},
    "Munich": {"days": 5}
}

# Define the direct flights
flights = {
    "Copenhagen": ["Dubrovnik", "Brussels", "Prague", "Santorini", "Athens", "Naples", "Munich"],
    "Dubrovnik": ["Copenhagen", "Naples", "Athens", "Geneva", "Munich"],
    "Brussels": ["Copenhagen", "Prague", "Naples", "Athens", "Munich", "Geneva"],
    "Prague": ["Copenhagen", "Brussels", "Athens", "Geneva", "Munich"],
    "Athens": ["Copenhagen", "Dubrovnik", "Naples", "Santorini", "Geneva", "Mykonos", "Brussels", "Munich", "Prague"],
    "Naples": ["Copenhagen", "Dubrovnik", "Athens", "Santorini", "Geneva", "Mykonos", "Brussels", "Munich", "Prague"],
    "Santorini": ["Copenhagen", "Athens", "Naples", "Geneva"],
    "Mykonos": ["Geneva", "Naples", "Athens", "Munich"],
    "Geneva": ["Prague", "Athens", "Naples", "Santorini", "Mykonos", "Brussels", "Munich", "Copenhagen"],
    "Munich": ["Copenhagen", "Dubrovnik", "Brussels", "Prague", "Athens", "Naples", "Mykonos", "Geneva"]
}

def is_valid_itinerary(itinerary):
    day = 1
    visited = set()
    for city, duration in itinerary:
        if city in visited:
            return False
        visited.add(city)
        if city in cities:
            if "must_visit" in cities[city]:
                start, end = cities[city]["must_visit"]
                if not (start <= day <= end or start <= day + duration - 1 <= end):
                    return False
        day += duration
    return day == 29

def find_optimal_itinerary():
    # Generate all permutations of cities
    for perm in permutations(cities.keys()):
        itinerary = []
        day = 1
        valid = True
        for city in perm:
            duration = cities[city]["days"]
            if not (day + duration - 1 <= 28):
                valid = False
                break
            itinerary.append((city, duration))
            day += duration
        if valid and is_valid_itinerary(itinerary):
            return itinerary
    return None

def generate_output(itinerary):
    output = []
    day = 1
    for city, duration in itinerary:
        output.append({"day_range": f"Day {day}-{day + duration - 1}", "place": city})
        day += duration
    return {"itinerary": output}

itinerary = find_optimal_itinerary()
if itinerary:
    print(json.dumps(generate_output(itinerary)))
else:
    print(json.dumps({"itinerary": []}))