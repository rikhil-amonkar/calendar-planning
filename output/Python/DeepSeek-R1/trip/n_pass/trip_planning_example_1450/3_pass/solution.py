import json

def build_graph():
    cities = ['Stockholm', 'Hamburg', 'Florence', 'Istanbul', 'Oslo', 'Vilnius', 'Santorini', 'Munich', 'Frankfurt', 'Krakow']
    graph = {city: [] for city in cities}
    
    # Bidirectional connections
    bidirectional_pairs = [
        ('Oslo', 'Stockholm'),
        ('Krakow', 'Frankfurt'),
        ('Krakow', 'Istanbul'),
        ('Munich', 'Stockholm'),
        ('Hamburg', 'Stockholm'),
        ('Oslo', 'Istanbul'),
        ('Istanbul', 'Stockholm'),
        ('Oslo', 'Krakow'),
        ('Vilnius', 'Istanbul'),
        ('Oslo', 'Vilnius'),
        ('Frankfurt', 'Istanbul'),
        ('Oslo', 'Frankfurt'),
        ('Munich', 'Hamburg'),
        ('Munich', 'Istanbul'),
        ('Oslo', 'Munich'),
        ('Oslo', 'Hamburg'),
        ('Vilnius', 'Frankfurt'),
        ('Krakow', 'Munich'),
        ('Hamburg', 'Istanbul'),
        ('Frankfurt', 'Stockholm'),
        ('Frankfurt', 'Munich'),
        ('Krakow', 'Stockholm'),
        ('Frankfurt', 'Hamburg')
    ]
    
    for a, b in bidirectional_pairs:
        graph[a].append(b)
        graph[b].append(a)
    
    # Unidirectional connections
    unidirectional_pairs = [
        ('Krakow', 'Vilnius'),
        ('Florence', 'Munich'),
        ('Stockholm', 'Santorini'),
        ('Santorini', 'Oslo'),
        ('Vilnius', 'Munich')
    ]
    
    for a, b in unidirectional_pairs:
        graph[a].append(b)
    
    return graph

# Adjusted durations to sum to 32 days
durations = {
    'Stockholm': 3,
    'Hamburg': 3,    # Reduced from 5
    'Florence': 1,    # Reduced from 2
    'Istanbul': 5,
    'Oslo': 3,        # Reduced from 5
    'Vilnius': 4,     # Reduced from 5
    'Santorini': 2,
    'Munich': 4,      # Reduced from 5
    'Frankfurt': 3,   # Reduced from 4
    'Krakow': 4       # Reduced from 5
}

def is_valid(path, graph):
    for i in range(1, len(path)):
        if path[i] not in graph[path[i-1]]:
            return False
    return True

def get_day_constraint_checks(path):
    current_day = 1
    krakow_ok = False
    istanbul_ok = False
    total_days = 0
    
    for city in path:
        end_day = current_day + durations[city] - 1
        # Check if day 5 is during this city's stay
        if city == 'Krakow':
            if current_day <= 5 <= end_day:
                krakow_ok = True
        # Check if day 25 is during this city's stay
        if city == 'Istanbul':
            if current_day <= 25 <= end_day:
                istanbul_ok = True
        current_day = end_day + 1
        total_days = end_day  # Last end_day is total trip days
    
    # Verify all constraints
    return krakow_ok and istanbul_ok and (total_days == 32)

def get_itinerary(path):
    itinerary = []
    day = 1
    for city in path:
        end_day = day + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {day}-{end_day}",
            "place": city
        })
        day = end_day + 1
    return itinerary

def backtrack(path, remaining, graph):
    if not remaining:
        if get_day_constraint_checks(path):
            return path
        return None
        
    for city in list(remaining):
        if path and city not in graph[path[-1]]:
            continue
        new_path = path + [city]
        new_remaining = remaining - {city}
        if not is_valid(new_path, graph):
            continue
        result = backtrack(new_path, new_remaining, graph)
        if result:
            return result
    return None

def main():
    graph = build_graph()
    cities_set = set(durations.keys())
    solution = backtrack([], cities_set, graph)
    if solution is None:
        print(json.dumps({"itinerary": []}))
        return
    
    itinerary_list = get_itinerary(solution)
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()