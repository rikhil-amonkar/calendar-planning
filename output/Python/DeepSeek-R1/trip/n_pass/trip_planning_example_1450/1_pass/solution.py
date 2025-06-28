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
        ('Frankfurt', 'Florence'),
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

def backtrack(path, remaining, graph):
    if len(path) == 10:
        try:
            idx_krakow = path.index('Krakow')
            prefix_sum_k = sum(durations[city] for city in path[:idx_krakow])
            start_k = 1 + prefix_sum_k - idx_krakow
            if start_k != 5:
                return None
            
            idx_istanbul = path.index('Istanbul')
            prefix_sum_i = sum(durations[city] for city in path[:idx_istanbul])
            start_i = 1 + prefix_sum_i - idx_istanbul
            if start_i != 25:
                return None
            
            return path[:]
        except ValueError:
            return None
    
    for next_city in list(remaining):
        if path:
            last_city = path[-1]
            if next_city not in graph[last_city]:
                continue
        new_path = path + [next_city]
        new_remaining = remaining - {next_city}
        result = backtrack(new_path, new_remaining, graph)
        if result is not None:
            return result
    return None

def main():
    graph = build_graph()
    cities_set = set(durations.keys())
    solution = backtrack([], cities_set, graph)
    if solution is None:
        print(json.dumps({"itinerary": []}))
        return
    
    itinerary_list = []
    cum_sum = 0
    for i, city in enumerate(solution):
        start = 1 + cum_sum - i
        end = start + durations[city] - 1
        day_range_str = f"Day {start}-{end}"
        itinerary_list.append({"day_range": day_range_str, "place": city})
        cum_sum += durations[city]
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()