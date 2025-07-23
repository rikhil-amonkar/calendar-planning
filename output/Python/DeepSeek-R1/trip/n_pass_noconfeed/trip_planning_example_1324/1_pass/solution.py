import json

def main():
    cities_list = ['Venice', 'Barcelona', 'Copenhagen', 'Lyon', 'Reykjavik', 'Dubrovnik', 'Athens', 'Tallinn', 'Munich']
    durations = {
        'Venice': 4,
        'Barcelona': 3,
        'Copenhagen': 4,
        'Lyon': 4,
        'Reykjavik': 4,
        'Dubrovnik': 5,
        'Athens': 2,
        'Tallinn': 5,
        'Munich': 3
    }
    
    constraints = {
        'Barcelona': (8, 12),
        'Copenhagen': (4, 10),
        'Dubrovnik': (12, 20)
    }
    
    edges = [
        ('Copenhagen', 'Athens'),
        ('Copenhagen', 'Dubrovnik'),
        ('Munich', 'Tallinn'),
        ('Copenhagen', 'Munich'),
        ('Venice', 'Munich'),
        ('Reykjavik', 'Athens'),
        ('Athens', 'Dubrovnik'),
        ('Venice', 'Athens'),
        ('Lyon', 'Barcelona'),
        ('Copenhagen', 'Reykjavik'),
        ('Reykjavik', 'Munich'),
        ('Athens', 'Munich'),
        ('Lyon', 'Munich'),
        ('Barcelona', 'Reykjavik'),
        ('Venice', 'Copenhagen'),
        ('Barcelona', 'Dubrovnik'),
        ('Lyon', 'Venice'),
        ('Dubrovnik', 'Munich'),
        ('Barcelona', 'Athens'),
        ('Copenhagen', 'Barcelona'),
        ('Venice', 'Barcelona'),
        ('Barcelona', 'Munich'),
        ('Barcelona', 'Tallinn'),
        ('Copenhagen', 'Tallinn')
    ]
    
    graph = {}
    for u, v in edges:
        if u not in graph:
            graph[u] = []
        if v not in graph:
            graph[v] = []
        graph[u].append(v)
        graph[v].append(u)
    
    stack = []
    stack.append(([], set(), 0))
    solution_path = None
    
    while stack:
        path, visited, total_duration = stack.pop()
        k = len(path)
        
        if k == 9:
            solution_path = path
            break
            
        for city in cities_list:
            if city in visited:
                continue
                
            if path:
                last_city = path[-1]
                if last_city not in graph or city not in graph[last_city]:
                    continue
                    
            start_day = 1 + total_duration - k
            if city in constraints:
                low, high = constraints[city]
                if start_day < low or start_day > high:
                    continue
                    
            new_path = path + [city]
            new_visited = visited | {city}
            new_total_duration = total_duration + durations[city]
            stack.append((new_path, new_visited, new_total_duration))
            
    if solution_path is None:
        print(json.dumps({"itinerary": []}))
        return
        
    itinerary_list = []
    total_so_far = 0
    for i, city in enumerate(solution_path):
        start_day = 1 + total_so_far - i
        duration_here = durations[city]
        end_day = start_day + duration_here - 1
        total_so_far += duration_here
        
        if start_day == end_day:
            day_range_str = f"Day {start_day}"
        else:
            day_range_str = f"Day {start_day}-{end_day}"
            
        itinerary_list.append({
            "day_range": day_range_str,
            "place": city
        })
        
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))
    
if __name__ == "__main__":
    main()