import itertools
import json

def main():
    cities = {
        'Vienna': 4,
        'Lyon': 3,
        'Edinburgh': 4,
        'Reykjavik': 5,
        'Stuttgart': 5,
        'Manchester': 2,
        'Split': 5,
        'Prague': 4
    }
    
    fixed_order = ['Stuttgart', 'Edinburgh', 'Prague']
    remaining_cities = [city for city in cities if city not in fixed_order]
    
    graph = {
        'Lyon': ['Vienna', 'Split'],
        'Reykjavik': ['Vienna'],
        'Manchester': ['Vienna', 'Split'],
        'Split': ['Lyon', 'Manchester', 'Vienna'],
        'Vienna': ['Lyon', 'Reykjavik', 'Manchester', 'Split']
    }
    
    found = False
    result_perm = None
    for perm in itertools.permutations(remaining_cities):
        valid = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in graph[perm[i]]:
                valid = False
                break
        if not valid:
            continue
            
        try:
            idx = perm.index('Split')
        except ValueError:
            continue
            
        if idx == 0 or idx == 4:
            continue
        elif idx == 1:
            if cities[perm[0]] < 4:
                continue
        elif idx == 3:
            total_first_three = cities[perm[0]] + cities[perm[1]] + cities[perm[2]]
            if total_first_three > 12:
                continue
                
        found = True
        result_perm = perm
        break
        
    if not found:
        itinerary = []
    else:
        order = fixed_order + list(result_perm)
        start_day = 1
        blocks = []
        for city in order:
            duration = cities[city]
            end_day = start_day + duration - 1
            blocks.append((city, start_day, end_day))
            start_day = end_day
        
        itinerary = []
        for city, start, end in blocks:
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range_str, "place": city})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == '__main__':
    main()