import json

graph = {
    'Copenhagen': ['Athens', 'Dubrovnik', 'Munich', 'Reykjavik', 'Barcelona', 'Venice', 'Tallinn'],
    'Athens': ['Copenhagen', 'Dubrovnik', 'Reykjavik', 'Venice', 'Munich', 'Barcelona'],
    'Dubrovnik': ['Copenhagen', 'Athens', 'Barcelona', 'Munich'],
    'Munich': ['Tallinn', 'Copenhagen', 'Venice', 'Reykjavik', 'Athens', 'Lyon', 'Barcelona', 'Dubrovnik'],
    'Venice': ['Munich', 'Athens', 'Copenhagen', 'Lyon', 'Barcelona'],
    'Reykjavik': ['Athens', 'Copenhagen', 'Munich', 'Barcelona'],
    'Lyon': ['Barcelona', 'Munich', 'Venice'],
    'Barcelona': ['Lyon', 'Reykjavik', 'Dubrovnik', 'Athens', 'Copenhagen', 'Venice', 'Munich', 'Tallinn'],
    'Tallinn': ['Munich', 'Barcelona', 'Copenhagen']
}

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

def dfs(current_path, current_start, remaining, durations, graph):
    n_remaining = len(remaining)
    if n_remaining == 0:
        return current_path
        
    T_remaining = sum(durations[c] for c in remaining)
    if current_start != 26 - T_remaining + n_remaining:
        return None
        
    if 'Barcelona' in remaining and current_start > 12:
        return None
    if 'Copenhagen' in remaining and current_start > 10:
        return None
    if 'Dubrovnik' in remaining and current_start > 20:
        return None
        
    for candidate in list(remaining):
        if current_path:
            last_city = current_path[-1]
            if candidate not in graph[last_city]:
                continue
                
        if candidate == 'Barcelona':
            if current_start < 8 or current_start > 12:
                continue
        elif candidate == 'Copenhagen':
            if current_start < 4 or current_start > 10:
                continue
        elif candidate == 'Dubrovnik':
            if current_start < 12 or current_start > 20:
                continue
                
        new_path = current_path + [candidate]
        new_start = current_start + durations[candidate] - 1
        new_remaining = remaining - {candidate}
        
        result = dfs(new_path, new_start, new_remaining, durations, graph)
        if result is not None:
            return result
            
    return None

all_cities = set(durations.keys())
solution_path = dfs([], 1, all_cities, durations, graph)

if solution_path is None:
    output_json = {"itinerary": []}
else:
    itinerary = []
    start_day = 1
    for city in solution_path:
        end_day = start_day + durations[city] - 1
        day_range_str = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range_str, "place": city})
        start_day = end_day
    output_json = {"itinerary": itinerary}

print(json.dumps(output_json))