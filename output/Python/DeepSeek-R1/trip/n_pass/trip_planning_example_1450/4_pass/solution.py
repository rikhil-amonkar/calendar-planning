import json

def build_graph():
    cities = ['Stockholm', 'Hamburg', 'Florence', 'Istanbul', 'Oslo', 'Vilnius', 'Santorini', 'Munich', 'Frankfurt', 'Krakow']
    graph = {city: [] for city in cities}
    
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
    
    unidirectional_pairs = [
        ('Krakow', 'Vilnius'),
        ('Florence', 'Munich'),
        ('Stockholm', 'Santorini'),
        ('Santorini', 'Oslo'),
        ('Vilnius', 'Munich')
    ]
    
    for a, b in unidirectional_pairs:
        graph[a].append(b)
        graph[b].append(a)
    
    return graph

durations = {
    'Stockholm': 3,
    'Hamburg': 3,
    'Florence': 1,
    'Istanbul': 5,
    'Oslo': 3,
    'Vilnius': 4,
    'Santorini': 2,
    'Munich': 4,
    'Frankfurt': 3,
    'Krakow': 4
}

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

def backtrack(path, current_day, remaining, graph, durations):
    if current_day > 32:
        return None
        
    if current_day > 5 and 'Krakow' not in path:
        return None
        
    if current_day > 25 and 'Istanbul' not in path:
        return None
        
    if not remaining:
        if current_day == 33:
            return path
        return None
        
    for city in remaining:
        if path and city not in graph[path[-1]]:
            continue
            
        start = current_day
        end = current_day + durations[city] - 1
        if city == 'Krakow':
            if not (start <= 5 <= end):
                continue
        if city == 'Istanbul':
            if not (start <= 25 <= end):
                continue
                
        new_path = path + [city]
        new_remaining = remaining - {city}
        new_day = current_day + durations[city]
        result = backtrack(new_path, new_day, new_remaining, graph, durations)
        if result is not None:
            return result
            
    return None

def main():
    graph = build_graph()
    cities_set = set(durations.keys())
    solution = None
    for start_city in cities_set:
        remaining = cities_set - {start_city}
        path = backtrack([start_city], 1 + durations[start_city], remaining, graph, durations)
        if path is not None:
            solution = [start_city] + path
            break
            
    if solution is None:
        print(json.dumps({"itinerary": []}))
        return
        
    itinerary_list = get_itinerary(solution)
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()