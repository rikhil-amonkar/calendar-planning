import json
from itertools import permutations

# Define the constraints
cities = {
    "Valencia": {"days": 2, "preferred_days": range(3, 5)},
    "Oslo": {"days": 3, "preferred_days": range(13, 16)},
    "Lyon": {"days": 4},
    "Prague": {"days": 3},
    "Paris": {"days": 4},
    "Nice": {"days": 4},
    "Seville": {"days": 5, "preferred_days": range(5, 10)},
    "Tallinn": {"days": 2},
    "Mykonos": {"days": 5, "preferred_days": range(21, 26)},
    "Lisbon": {"days": 2}
}

# Define the direct flight connections
connections = [
    ("Lisbon", "Paris"), ("Lyon", "Nice"), ("Tallinn", "Oslo"), ("Prague", "Lyon"),
    ("Paris", "Oslo"), ("Lisbon", "Seville"), ("Prague", "Lisbon"), ("Oslo", "Nice"),
    ("Valencia", "Paris"), ("Valencia", "Lisbon"), ("Paris", "Nice"), ("Nice", "Mykonos"),
    ("Paris", "Lyon"), ("Valencia", "Lyon"), ("Prague", "Oslo"), ("Prague", "Paris"),
    ("Seville", "Paris"), ("Oslo", "Lyon"), ("Prague", "Valencia"), ("Lisbon", "Nice"),
    ("Lisbon", "Oslo"), ("Valencia", "Seville"), ("Lisbon", "Lyon"), ("Paris", "Tallinn"),
    ("Prague", "Tallinn")
]

def is_valid_itinerary(itinerary):
    current_day = 1
    for city, duration in itinerary:
        city_info = cities[city]
        if "preferred_days" in city_info:
            preferred_days = city_info["preferred_days"]
            if not any(current_day + i - 1 in preferred_days for i in range(duration)):
                return False
        current_day += duration
    return current_day == 26

def generate_itineraries():
    all_cities = list(cities.keys())
    for perm in permutations(all_cities):
        itinerary = [(city, cities[city]["days"]) for city in perm]
        if is_valid_itinerary(itinerary) and is_connected(itinerary):
            return itinerary
    return None

def is_connected(itinerary):
    current_city = itinerary[0][0]
    for next_city, _ in itinerary[1:]:
        if (current_city, next_city) not in connections and (next_city, current_city) not in connections:
            return False
        current_city = next_city
    return True

def create_itinerary_json(itinerary):
    result = []
    current_day = 1
    for city, duration in itinerary:
        result.append({"day_range": f"Day {current_day}-{current_day + duration - 1}", "place": city})
        current_day += duration
    return {"itinerary": result}

# Generate the itinerary
itinerary = generate_itineraries()

# Output the itinerary as JSON
print(json.dumps(create_itinerary_json(itinerary)))