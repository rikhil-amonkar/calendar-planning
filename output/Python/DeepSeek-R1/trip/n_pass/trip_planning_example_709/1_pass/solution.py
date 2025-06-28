import json
from itertools import permutations

def main():
    graph = {
        'Helsinki': ['Prague', 'Reykjavik', 'Dubrovnik'],
        'Prague': ['Helsinki', 'Valencia', 'Reykjavik'],
        'Valencia': ['Prague', 'Porto'],
        'Porto': ['Valencia'],
        'Reykjavik': ['Helsinki', 'Prague'],
        'Dubrovnik': ['Helsinki']
    }
    
    days_map = {
        'Helsinki': 4,
        'Valencia': 5,
        'Dubrovnik': 4,
        'Porto': 3,
        'Prague': 3,
        'Reykjavik': 4
    }
    
    fixed_tail = ['Prague', 'Valencia', 'Porto']
    all_cities = list(days_map.keys())
    head_cities = [city for city in all_cities if city not in fixed_tail]
    
    candidates = []
    for perm in permutations(head_cities):
        valid_path = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in graph[perm[i]]:
                valid_path = False
                break
        if valid_path and perm[-1] in graph['Prague']:
            full_path = list(perm) + fixed_tail
            candidates.append(full_path)
    
    if candidates:
        candidate_path = candidates[0]
    else:
        candidate_path = ['Dubrovnik', 'Helsinki', 'Reykjavik', 'Prague', 'Valencia', 'Porto']
    
    start_day = 1
    itinerary_list = []
    for city in candidate_path:
        end_day = start_day + days_map[city] - 1
        day_range_str = f"Day {start_day}-{end_day}"
        itinerary_list.append({"day_range": day_range_str, "place": city})
        start_day = end_day
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == '__main__':
    main()