import itertools
import json

def main():
    cities = ['Amsterdam', 'Edinburgh', 'Brussels', 'Vienna', 'Berlin', 'Reykjavik']
    required_days = {
        'Amsterdam': 4,
        'Edinburgh': 5,
        'Brussels': 5,
        'Vienna': 5,
        'Berlin': 4,
        'Reykjavik': 5
    }
    constraints = {
        'Amsterdam': (5, 8),
        'Berlin': (16, 19),
        'Reykjavik': (12, 16)
    }
    graph = {
        'Edinburgh': ['Berlin', 'Amsterdam', 'Brussels'],
        'Amsterdam': ['Berlin', 'Edinburgh', 'Reykjavik', 'Vienna'],
        'Berlin': ['Edinburgh', 'Amsterdam', 'Vienna', 'Brussels', 'Reykjavik'],
        'Brussels': ['Edinburgh', 'Berlin', 'Vienna', 'Reykjavik'],
        'Vienna': ['Berlin', 'Reykjavik', 'Brussels', 'Amsterdam'],
        'Reykjavik': ['Vienna', 'Amsterdam', 'Brussels', 'Berlin']
    }
    
    for perm in itertools.permutations(cities):
        valid_path = True
        for i in range(len(perm)-1):
            if perm[i+1] not in graph[perm[i]]:
                valid_path = False
                break
        if not valid_path:
            continue
            
        d = [0] * len(perm)
        d[0] = required_days[perm[0]]
        for i in range(1, len(perm)):
            d[i] = d[i-1] + required_days[perm[i]] - 1
        
        if d[-1] != 23:
            continue
            
        meets_constraints = True
        for city, (low, high) in constraints.items():
            if city not in perm:
                meets_constraints = False
                break
            idx = perm.index(city)
            start = 1 if idx == 0 else d[idx-1]
            end = d[idx]
            if not (start <= high and end >= low):
                meets_constraints = False
                break
                
        if meets_constraints:
            itinerary_list = []
            itinerary_list.append({"day_range": f"Day 1-{d[0]}", "place": perm[0]})
            for i in range(1, len(perm)):
                itinerary_list.append({"day_range": f"Day {d[i-1]}-{d[i]}", "place": perm[i]})
            print(json.dumps({"itinerary": itinerary_list}))
            return
            
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()