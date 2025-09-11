import itertools
import json

def main():
    cities = {
        'Reykjavik': {'days': 2, 'event': (3, 4)},
        'Stockholm': {'days': 2, 'event': (4, 5)},
        'Porto': {'days': 5, 'event': (13, 17)},
        'Nice': {'days': 3},
        'Venice': {'days': 4},
        'Vienna': {'days': 3, 'event': (11, 13)},
        'Split': {'days': 3},
        'Copenhagen': {'days': 2}
    }
    
    graph = {
        'Copenhagen': ['Vienna', 'Split', 'Stockholm', 'Reykjavik', 'Nice', 'Venice', 'Porto'],
        'Nice': ['Stockholm', 'Reykjavik', 'Porto', 'Venice', 'Vienna', 'Copenhagen'],
        'Split': ['Copenhagen', 'Vienna', 'Stockholm'],
        'Reykjavik': ['Nice', 'Vienna', 'Copenhagen', 'Stockholm'],
        'Stockholm': ['Nice', 'Copenhagen', 'Split', 'Vienna', 'Reykjavik'],
        'Venice': ['Nice', 'Vienna', 'Copenhagen'],
        'Vienna': ['Copenhagen', 'Reykjavik', 'Nice', 'Stockholm', 'Split', 'Venice', 'Porto'],
        'Porto': ['Nice', 'Copenhagen', 'Vienna']
    }
    
    city_names = list(cities.keys())
    
    for perm in itertools.permutations(city_names):
        valid_order = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in graph[perm[i]]:
                valid_order = False
                break
                
        if not valid_order:
            continue
            
        s = [0] * 8
        e = [0] * 8
        s[0] = 1
        e[0] = s[0] + cities[perm[0]]['days'] - 1
        for i in range(1, 8):
            s[i] = e[i-1]
            e[i] = s[i] + cities[perm[i]]['days'] - 1
            
        valid_events = True
        for i in range(8):
            city = perm[i]
            if 'event' in cities[city]:
                event_start, event_end = cities[city]['event']
                if not (s[i] <= event_end and e[i] >= event_start):
                    valid_events = False
                    break
                    
        if valid_events:
            itinerary = []
            for i in range(8):
                start = s[i]
                end = e[i]
                if start == end:
                    day_range_str = f"Day {start}"
                else:
                    day_range_str = f"Day {start}-{end}"
                itinerary.append({"day_range": day_range_str, "place": perm[i]})
                
            result = {"itinerary": itinerary}
            print(json.dumps(result))
            return
            
    print('{"itinerary": []}')

if __name__ == "__main__":
    main()