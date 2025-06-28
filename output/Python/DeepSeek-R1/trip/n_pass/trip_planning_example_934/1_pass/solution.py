import itertools
import json

def main():
    cities_6 = ['Brussels', 'Rome', 'Dubrovnik', 'Geneva', 'Riga', 'Valencia']
    durations = {
        'Brussels': 5,
        'Rome': 2,
        'Dubrovnik': 3,
        'Geneva': 5,
        'Riga': 4,
        'Valencia': 2
    }
    
    graph = {
        'Brussels': set(['Valencia', 'Geneva', 'Riga', 'Rome']),
        'Rome': set(['Valencia', 'Geneva', 'Brussels', 'Riga', 'Dubrovnik']),
        'Dubrovnik': set(['Geneva', 'Rome']),
        'Geneva': set(['Brussels', 'Rome', 'Dubrovnik', 'Valencia']),
        'Riga': set(['Rome', 'Brussels']),
        'Valencia': set(['Brussels', 'Rome', 'Geneva'])
    }
    
    valid_last_cities = {'Brussels', 'Rome', 'Geneva'}
    
    found = False
    valid_perm = None
    valid_start_days = None
    
    for perm in itertools.permutations(cities_6):
        valid_path = True
        for i in range(len(perm)-1):
            if perm[i+1] not in graph[perm[i]]:
                valid_path = False
                break
        if not valid_path:
            continue
            
        if perm[-1] not in valid_last_cities:
            continue
            
        start_days = [1] * 6
        for i in range(1, 6):
            start_days[i] = start_days[i-1] + durations[perm[i-1]] - 1
            
        meets_constraints = True
        for i in range(6):
            city = perm[i]
            s = start_days[i]
            if city == 'Brussels':
                if s < 3 or s > 11:
                    meets_constraints = False
                    break
            if city == 'Riga':
                if s < 1 or s > 7:
                    meets_constraints = False
                    break
                    
        if meets_constraints:
            found = True
            valid_perm = perm
            valid_start_days = start_days
            break
            
    if not found:
        print(json.dumps({"itinerary": []}))
        return
        
    itinerary_list = []
    for i in range(6):
        start = valid_start_days[i]
        end = start + durations[valid_perm[i]] - 1
        day_range_str = f"Day {start}-{end}"
        itinerary_list.append({
            "day_range": day_range_str,
            "place": valid_perm[i]
        })
        
    itinerary_list.append({
        "day_range": "Day 16-17",
        "place": "Budapest"
    })
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))
    
if __name__ == "__main__":
    main()