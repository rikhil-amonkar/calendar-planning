import json
from datetime import timedelta

# Define the constraints
constraints = {
    "Copenhagen": {"days": 5, "must_visit": [11, 12, 13, 14, 15]},
    "Geneva": {"days": 3},
    "Mykonos": {"days": 2, "must_visit": [27, 28]},
    "Naples": {"days": 4, "must_visit": [5, 6, 7, 8]},
    "Prague": {"days": 2},
    "Dubrovnik": {"days": 3},
    "Athens": {"days": 4, "must_visit": [8, 9, 10, 11]},
    "Santorini": {"days": 5},
    "Brussels": {"days": 4},
    "Munich": {"days": 5}
}

# Define the direct flight connections
connections = {
    "Copenhagen": ["Dubrovnik", "Brussels", "Prague", "Naples", "Athens", "Munich", "Santorini"],
    "Dubrovnik": ["Copenhagen", "Naples", "Athens", "Geneva", "Munich"],
    "Brussels": ["Copenhagen", "Naples", "Athens", "Munich", "Prague", "Geneva"],
    "Prague": ["Copenhagen", "Geneva", "Athens", "Brussels", "Munich"],
    "Geneva": ["Prague", "Athens", "Dubrovnik", "Mykonos", "Naples", "Brussels", "Munich", "Santorini"],
    "Mykonos": ["Geneva", "Naples", "Athens", "Munich"],
    "Naples": ["Copenhagen", "Dubrovnik", "Athens", "Mykonos", "Munich", "Brussels", "Geneva", "Santorini"],
    "Athens": ["Copenhagen", "Dubrovnik", "Geneva", "Mykonos", "Naples", "Prague", "Santorini", "Munich", "Brussels"],
    "Santorini": ["Geneva", "Naples", "Athens"],
    "Munich": ["Copenhagen", "Dubrovnik", "Brussels", "Prague", "Geneva", "Mykonos", "Naples", "Athens"]
}

def find_itinerary(constraints, connections):
    itinerary = []
    current_day = 1
    remaining_cities = list(constraints.keys())
    
    def can_stay(city, start_day, duration):
        end_day = start_day + duration - 1
        if end_day > 28:
            return False
        if city in constraints:
            must_visit_days = constraints[city].get("must_visit", [])
            for day in must_visit_days:
                if day < start_day or day > end_day:
                    return False
        return True
    
    def get_next_city(current_city, start_day):
        for city in remaining_cities:
            if current_city is None or (city != current_city and city in connections[current_city]):
                duration = constraints[city]["days"]
                if can_stay(city, start_day, duration):
                    return city
        return None
    
    while current_day <= 28 and remaining_cities:
        current_city = None if not itinerary else itinerary[-1]["place"]
        next_city = get_next_city(current_city, current_day)
        
        if next_city:
            duration = constraints[next_city]["days"]
            itinerary.append({"day_range": f"Day {current_day}-{current_day + duration - 1}", "place": next_city})
            current_day += duration
            remaining_cities.remove(next_city)
        else:
            break
    
    return itinerary

itinerary = find_itinerary(constraints, connections)
print(json.dumps({"itinerary": itinerary}, indent=2))