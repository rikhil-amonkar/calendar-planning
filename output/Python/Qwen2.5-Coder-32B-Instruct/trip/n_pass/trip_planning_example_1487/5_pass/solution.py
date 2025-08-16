import json

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
    def backtrack(current_itinerary, current_day, remaining_cities):
        if current_day > 28:
            return None
        if not remaining_cities and current_day == 28:
            return current_itinerary
        
        for i, city in enumerate(remaining_cities):
            duration = cities[city]["days"]
            if current_day + duration - 1 <= 28:
                new_itinerary = current_itinerary + [(city, duration)]
                result = backtrack(new_itinerary, current_day + duration, remaining_cities[:i] + remaining_cities[i+1:])
                if result and is_valid_itinerary(result):
                    return result
        return None
    
    all_cities = list(cities.keys())
    return backtrack([], 1, all_cities)

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