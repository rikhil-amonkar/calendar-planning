import itertools
import json

def main():
    cities = ['Barcelona', 'Venice', 'Naples', 'Valencia', 'Stuttgart', 'Split', 'Amsterdam', 'Nice', 'Porto']
    
    req_days = {
        'Barcelona': 2,
        'Venice': 5,
        'Naples': 3,
        'Valencia': 5,
        'Stuttgart': 2,
        'Split': 5,
        'Amsterdam': 4,
        'Nice': 2,
        'Porto': 4
    }
    
    graph = {
        'Venice': ['Nice', 'Amsterdam', 'Stuttgart', 'Naples', 'Barcelona'],
        'Naples': ['Amsterdam', 'Split', 'Barcelona', 'Nice', 'Valencia', 'Stuttgart'],
        'Barcelona': ['Nice', 'Porto', 'Valencia', 'Naples', 'Venice', 'Amsterdam', 'Stuttgart', 'Split'],
        'Valencia': ['Stuttgart', 'Amsterdam', 'Barcelona', 'Naples', 'Porto'],
        'Stuttgart': ['Valencia', 'Porto', 'Split', 'Amsterdam', 'Barcelona', 'Naples', 'Venice'],
        'Split': ['Stuttgart', 'Naples', 'Amsterdam', 'Barcelona'],
        'Amsterdam': ['Naples', 'Nice', 'Valencia', 'Barcelona', 'Split', 'Porto', 'Venice', 'Stuttgart'],
        'Nice': ['Venice', 'Barcelona', 'Amsterdam', 'Naples', 'Porto'],
        'Porto': ['Barcelona', 'Stuttgart', 'Valencia', 'Amsterdam', 'Nice']
    }
    
    for perm in itertools.permutations(cities):
        valid = True
        for i in range(len(perm)-1):
            if perm[i+1] not in graph[perm[i]]:
                valid = False
                break
        if not valid:
            continue
            
        start = [0] * len(perm)
        end = [0] * len(perm)
        start[0] = 1
        end[0] = start[0] + req_days[perm[0]] - 1
        
        for i in range(1, len(perm)):
            start[i] = end[i-1]
            end[i] = start[i] + req_days[perm[i]] - 1
            
        if end[-1] != 24:
            continue
            
        idx_barcelona = perm.index('Barcelona')
        if not (start[idx_barcelona] <= 5 and end[idx_barcelona] >= 6):
            continue
            
        idx_venice = perm.index('Venice')
        if not (start[idx_venice] <= 6 and end[idx_venice] >= 10):
            continue
            
        idx_naples = perm.index('Naples')
        if not (start[idx_naples] <= 20 and end[idx_naples] >= 18):
            continue
            
        idx_nice = perm.index('Nice')
        if not (start[idx_nice] <= 24 and end[idx_nice] >= 23):
            continue
            
        itinerary = []
        for i in range(len(perm)):
            if start[i] == end[i]:
                day_range = f"Day {start[i]}"
            else:
                day_range = f"Day {start[i]}-{end[i]}"
            itinerary.append({"day_range": day_range, "place": perm[i]})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
        return
        
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()