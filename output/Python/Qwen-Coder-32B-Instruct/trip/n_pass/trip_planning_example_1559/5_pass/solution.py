import json

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
connections = set([
    ("Lisbon", "Paris"), ("Lyon", "Nice"), ("Tallinn", "Oslo"), ("Prague", "Lyon"),
    ("Paris", "Oslo"), ("Lisbon", "Seville"), ("Prague", "Lisbon"), ("Oslo", "Nice"),
    ("Valencia", "Paris"), ("Valencia", "Lisbon"), ("Paris", "Nice"), ("Nice", "Mykonos"),
    ("Paris", "Lyon"), ("Valencia", "Lyon"), ("Prague", "Oslo"), ("Prague", "Paris"),
    ("Seville", "Paris"), ("Oslo", "Lyon"), ("Prague", "Valencia"), ("Lisbon", "Nice"),
    ("Lisbon", "Oslo"), ("Valencia", "Seville"), ("Lisbon", "Lyon"), ("Paris", "Tallinn"),
    ("Prague", "Tallinn")
])

def is_valid_day(city, current_day, duration):
    if "preferred_days" in cities[city]:
        preferred_days = cities[city]["preferred_days"]
        return all(current_day + i - 1 in preferred_days for i in range(duration))
    return True

def backtrack(current_city, current_day, visited, itinerary):
    if current_day > 25:
        return None
    
    if current_day == 25:
        # Check if we can finish with the current city
        if is_valid_day(current_city, current_day, 1):
            return itinerary + [(current_city, 1)]
        return None
    
    for city in cities:
        if city not in visited and ((current_city, city) in connections or (city, current_city) in connections):
            if is_valid_day(city, current_day, cities[city]["days"]):
                visited.add(city)
                new_itinerary = itinerary + [(city, cities[city]["days"])]
                result = backtrack(city, current_day + cities[city]["days"], visited, new_itinerary)
                if result:
                    return result
                visited.remove(city)  # Only remove if we added it
    
    return None

def generate_itinerary():
    for start_city in cities:
        for start_day in range(1, 26 - cities[start_city]["days"] + 1):
            if is_valid_day(start_city, start_day, cities[start_city]["days"]):
                visited = {start_city}
                itinerary = [(start_city, cities[start_city]["days"])]
                result = backtrack(start_city, start_day + cities[start_city]["days"], visited, itinerary)
                if result and sum(day for _, day in result) == 25 - start_day + 1:
                    return [(start_city, start_day)] + result
    return None

def create_itinerary_json(itinerary):
    result = []
    current_day = 1
    for city, duration in itinerary:
        result.append({"day_range": f"Day {current_day}-{current_day + duration - 1}", "place": city})
        current_day += duration
    return {"itinerary": result}

# Generate the itinerary
itinerary = generate_itinerary()

# Output the itinerary as JSON
if itinerary:
    print(json.dumps(create_itinerary_json(itinerary), indent=4))
else:
    print("No valid itinerary found.")