import itertools
import json

def main():
    graph = {
        'Helsinki': {'Prague', 'Reykjavik', 'Dubrovnik'},
        'Prague': {'Helsinki', 'Valencia', 'Reykjavik'},
        'Valencia': {'Prague', 'Porto'},
        'Porto': {'Valencia'},
        'Reykjavik': {'Helsinki', 'Prague'},
        'Dubrovnik': {'Helsinki'}
    }
    
    durations = {
        'Helsinki': 4,
        'Valencia': 5,
        'Dubrovnik': 4,
        'Porto': 3,
        'Prague': 3,
        'Reykjavik': 4
    }
    
    cities = list(durations.keys())
    found = False
    valid_perm = None
    
    for perm in itertools.permutations(cities):
        valid_path = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in graph[perm[i]]:
                valid_path = False
                break
        if not valid_path:
            continue
        
        try:
            idx = perm.index('Porto')
        except ValueError:
            continue
        
        s = 1
        for j in range(idx):
            s += (durations[perm[j]] - 1)
        if s >= 14 and s <= 16:
            found = True
            valid_perm = perm
            break
    
    if found:
        itinerary_list = []
        current_start = 1
        for city in valid_perm:
            end_day = current_start + durations[city] - 1
            if current_start == end_day:
                day_range_str = f"Day {current_start}"
            else:
                day_range_str = f"Day {current_start}-{end_day}"
            itinerary_list.append({
                "day_range": day_range_str,
                "place": city
            })
            current_start = end_day
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()