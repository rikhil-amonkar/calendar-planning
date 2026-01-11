import json
from itertools import permutations

# Direct flights graph
graph = {
    'Mykonos': ['Nice', 'Zurich'],
    'Nice': ['Mykonos', 'Riga', 'Zurich'],
    'Zurich': ['Mykonos', 'Prague', 'Riga', 'Bucharest', 'Valencia', 'Nice'],
    'Prague': ['Bucharest', 'Zurich', 'Riga', 'Valencia'],
    'Bucharest': ['Prague', 'Valencia', 'Riga', 'Zurich'],
    'Valencia': ['Bucharest', 'Zurich', 'Prague'],
    'Riga': ['Nice', 'Zurich', 'Bucharest', 'Prague']
}

# Required days in each city
required_days = {
    'Valencia': 5,
    'Riga': 5,
    'Prague': 3,
    'Mykonos': 3,
    'Zurich': 5,
    'Bucharest': 5,
    'Nice': 2
}

# Fixed constraints
fixed_events = [
    ('Mykonos', 1, 3),   # Mykonos days 1-3
    ('Prague', 7, 9)     # Prague days 7-9
]

def is_path_valid(path):
    # Check direct flights between consecutive cities
    for i in range(len(path) - 1):
        if path[i+1] not in graph[path[i]]:
            return False
    return True

def generate_itinerary(path):
    # Assign days to cities in path, respecting required days
    # We start at day 1
    day = 1
    itinerary = []
    for i, city in enumerate(path):
        needed = required_days[city]
        start_day = day
        # If we are not the first city, the first day of this city is also a travel day from previous city
        # That means the previous city also gets this day counted
        # So we just assign needed consecutive days starting at 'day'
        end_day = day + needed - 1
        itinerary.append((start_day, end_day, city))
        day = end_day + 1  # next city starts the day after
    return itinerary

def check_fixed_events(itinerary):
    # itinerary is list of (start, end, city)
    for city, req_start, req_end in fixed_events:
        found = False
        for start, end, c in itinerary:
            if c == city:
                # Check if required days are within this block
                if start <= req_start <= end and start <= req_end <= end:
                    found = True
                    break
        if not found:
            return False
    return True

def total_days(itinerary):
    # Last end day
    return itinerary[-1][1]

def solve():
    cities = list(required_days.keys())
    valid_paths = []
    
    # We know Mykonos must be first (day 1-3)
    remaining = [c for c in cities if c != 'Mykonos']
    for perm in permutations(remaining):
        path = ['Mykonos'] + list(perm)
        if not is_path_valid(path):
            continue
        itinerary = generate_itinerary(path)
        if total_days(itinerary) != 22:
            continue
        if not check_fixed_events(itinerary):
            continue
        valid_paths.append((path, itinerary))
    
    if not valid_paths:
        return None
    
    # Pick first valid path
    path, itinerary = valid_paths[0]
    
    # Format output
    result = {"itinerary": []}
    for start, end, city in itinerary:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        result["itinerary"].append({"day_range": day_range, "place": city})
    
    return result

if __name__ == "__main__":
    solution = solve()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}, indent=2))