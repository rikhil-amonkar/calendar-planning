import json
from itertools import permutations

def main():
    total_days = 15
    cities = {
        'Madrid': {'days': 7, 'constraints': [('must_be', 1, 7)]},
        'Bucharest': {'days': 2, 'constraints': [('must_be', 14, 15)]},
        'Paris': {'days': 6},
        'Seville': {'days': 3}
    }
    
    graph = {
        'Paris': ['Bucharest', 'Seville', 'Madrid'],
        'Seville': ['Paris', 'Madrid'],
        'Madrid': ['Paris', 'Seville', 'Bucharest'],
        'Bucharest': ['Paris', 'Madrid']
    }
    
    inter = [city for city in cities if city not in ['Madrid', 'Bucharest']]
    all_perms = list(permutations(inter))
    found = False
    result_itinerary = None
    
    for perm in all_perms:
        path = ['Madrid'] + list(perm) + ['Bucharest']
        valid_path = True
        for i in range(len(path)-1):
            if path[i+1] not in graph[path[i]]:
                valid_path = False
                break
        if not valid_path:
            continue
            
        current_day = 1
        itinerary_segments = []
        for city in path:
            duration = cities[city]['days']
            end_day = current_day + duration - 1
            if end_day > total_days:
                valid_path = False
                break
            itinerary_segments.append((current_day, end_day, city))
            current_day = end_day
        
        if not valid_path or itinerary_segments[-1][1] != total_days:
            continue
            
        valid_constraints = True
        for city, info in cities.items():
            if 'constraints' in info:
                for constr in info['constraints']:
                    if constr[0] == 'must_be':
                        low = constr[1]
                        high = constr[2]
                        seg_found = None
                        for seg in itinerary_segments:
                            if seg[2] == city:
                                seg_found = seg
                                break
                        if seg_found is None:
                            valid_constraints = False
                        else:
                            s, e, _ = seg_found
                            if not (s <= low and e >= high):
                                valid_constraints = False
        if not valid_constraints:
            continue
            
        found = True
        itinerary_output = []
        for seg in itinerary_segments:
            s, e, city = seg
            if s == e:
                day_range_str = f"Day {s}"
            else:
                day_range_str = f"Day {s}-{e}"
            itinerary_output.append({"day_range": day_range_str, "place": city})
        result_itinerary = {"itinerary": itinerary_output}
        break
        
    if not found:
        result_itinerary = {"itinerary": []}
        
    print(json.dumps(result_itinerary))

if __name__ == '__main__':
    main()