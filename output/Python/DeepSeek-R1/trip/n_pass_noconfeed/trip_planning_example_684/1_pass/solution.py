import itertools
import json

def main():
    stays = {
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
        'Brussels': ['Berlin', 'Edinburgh', 'Vienna', 'Reykjavik'],
        'Vienna': ['Berlin', 'Reykjavik', 'Brussels', 'Amsterdam'],
        'Berlin': ['Edinburgh', 'Amsterdam', 'Vienna', 'Brussels', 'Reykjavik'],
        'Reykjavik': ['Vienna', 'Amsterdam', 'Brussels', 'Berlin']
    }
    
    cities = list(stays.keys())
    found = False
    result_itinerary = None
    
    for perm in itertools.permutations(cities):
        valid_flight = True
        for i in range(len(perm)-1):
            if perm[i+1] not in graph[perm[i]]:
                valid_flight = False
                break
        if not valid_flight:
            continue
        
        start_days = [1]
        for i in range(1, len(perm)):
            start_days.append(start_days[i-1] + stays[perm[i-1]] - 1)
        
        meets_constraints = True
        for i, city in enumerate(perm):
            if city in constraints:
                s = start_days[i]
                e = s + stays[city] - 1
                low, high = constraints[city]
                if e < low or s > high:
                    meets_constraints = False
                    break
        if meets_constraints:
            found = True
            itinerary_list = []
            for i, city in enumerate(perm):
                start = start_days[i]
                end = start + stays[city] - 1
                day_range_str = f"Day {start}-{end}"
                itinerary_list.append({"day_range": day_range_str, "place": city})
            result_itinerary = itinerary_list
            break
    
    if not found:
        result_itinerary = []
    
    print(json.dumps({"itinerary": result_itinerary}))

if __name__ == "__main__":
    main()