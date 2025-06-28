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
    'Venice': 3,
    'Barcelona': 3,
    'Copenhagen': 3,
    'Lyon': 3,
    'Reykjavik': 3,
    'Dubrovnik': 4,
    'Athens': 1,
    'Tallinn': 4,
    'Munich': 2
}

def iterative_dfs():
    all_cities = set(durations.keys())
    stack = [(['Tallinn'], 1 + durations['Tallinn'], all_cities - {'Tallinn'})]
    
    while stack:
        current_path, current_start, remaining = stack.pop()
        if not remaining:
            if current_start == 27:  # Last city ended on day 26
                return current_path
            continue
            
        for candidate in list(remaining):
            if current_path[-1] != candidate and candidate not in graph[current_path[-1]]:
                continue
                
            # Calculate start and end days for candidate
            start_day = current_start
            end_day = start_day + durations[candidate] - 1
            
            # Check if exceeds total days
            if end_day > 26:
                continue
                
            # Check specific day constraints
            if candidate == 'Copenhagen':
                if not (start_day <= 5 <= end_day):
                    continue
            elif candidate == 'Barcelona':
                if not (start_day <= 10 <= end_day):
                    continue
            elif candidate == 'Dubrovnik':
                if not (start_day <= 14 <= end_day):
                    continue
                    
            new_path = current_path + [candidate]
            new_start = end_day + 1
            new_remaining = remaining - {candidate}
            stack.append((new_path, new_start, new_remaining))
            
    return None

solution_path = iterative_dfs()

if not solution_path or solution_path[-1] != 'Lyon':
    output_json = {"itinerary": []}
else:
    itinerary = []
    start_day = 1
    for city in solution_path:
        end_day = start_day + durations[city] - 1
        day_range_str = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range_str, "place": city})
        start_day = end_day + 1
    output_json = {"itinerary": itinerary}

print(json.dumps(output_json))