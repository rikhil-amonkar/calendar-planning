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

durations = {
    'Stockholm': 3,
    'Hamburg': 5,
    'Florence': 2,
    'Istanbul': 5,
    'Oslo': 5,
    'Vilnius': 5,
    'Santorini': 2,
    'Munich': 5,
    'Frankfurt': 4,
    'Krakow': 5
}

def is_valid(path, graph):
    for i in range(1, len(path)):
        if path[i] not in graph[path[i-1]]:
            return False
    return True

def get_day_constraint_checks(path):
    # Krakow must be the fifth day of the trip
    # Istanbul must be the twenty-fifth day of the trip
    day = 1
    for idx, city in enumerate(path):
        if city == 'Krakow':
            if day != 5:
                return False
        if city == 'Istanbul':
            if day != 25:
                return False
        day += durations[city]
    return True

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