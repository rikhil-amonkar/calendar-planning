import json
import itertools

def main():
    cities = ['Oslo', 'Stuttgart', 'Split', 'Geneva', 'Porto', 'Tallinn', 'Stockholm']
    requirements = {
        'Reykjavik': 2,
        'Oslo': 5,
        'Stuttgart': 5,
        'Split': 3,
        'Geneva': 2,
        'Porto': 3,
        'Tallinn': 5,
        'Stockholm': 3
    }
    
    graph = {
        'Reykjavik': {'Stuttgart', 'Stockholm', 'Tallinn', 'Oslo'},
        'Oslo': {'Reykjavik', 'Stockholm', 'Split', 'Tallinn', 'Geneva', 'Porto'},
        'Stuttgart': {'Reykjavik', 'Porto', 'Split', 'Stockholm'},
        'Split': {'Stockholm', 'Stuttgart', 'Oslo', 'Geneva'},
        'Geneva': {'Stockholm', 'Oslo', 'Split', 'Porto'},
        'Porto': {'Stuttgart', 'Oslo', 'Geneva'},
        'Tallinn': {'Oslo'},
        'Stockholm': {'Reykjavik', 'Stuttgart', 'Split', 'Geneva', 'Oslo'}
    }
    
    found = False
    itinerary_result = []
    
    non_reykjavik = cities
    for r in range(1, len(non_reykjavik) + 1):
        for subset in itertools.combinations(non_reykjavik, r):
            total_days = sum(requirements[city] for city in subset)
            if total_days != 17:
                continue
                
            for perm in itertools.permutations(subset):
                if perm[0] not in graph['Reykjavik']:
                    continue
                
                valid_path = True
                for i in range(len(perm) - 1):
                    if perm[i+1] not in graph[perm[i]]:
                        valid_path = False
                        break
                if not valid_path:
                    continue
                    
                if perm[-1] not in graph['Reykjavik']:
                    continue
                    
                current_start = 3
                last_end = None
                for city in perm:
                    end_day = current_start + requirements[city] - 1
                    if city == 'Stockholm':
                        if not (current_start <= 4 <= end_day):
                            valid_path = False
                            break
                    if city == 'Porto':
                        if not (current_start <= 18 <= end_day):
                            valid_path = False
                            break
                    current_start = end_day + 1
                    last_end = end_day
                
                if not valid_path:
                    continue
                    
                if last_end != 19:
                    continue
                    
                found = True
                full_itinerary = []
                full_itinerary.append({"day_range": "Day 1-2", "place": "Reykjavik"})
                current = 3
                for city in perm:
                    start = current
                    end = current + requirements[city] - 1
                    full_itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
                    current = end + 1
                full_itinerary.append({"day_range": "Day 20-21", "place": "Reykjavik"})
                itinerary_result = full_itinerary
                break
            if found:
                break
        if found:
            break
            
    if found:
        print(json.dumps({"itinerary": itinerary_result}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()