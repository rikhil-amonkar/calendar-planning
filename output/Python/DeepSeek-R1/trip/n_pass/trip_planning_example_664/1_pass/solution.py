import itertools
import json

def main():
    cities = ['Bucharest', 'Munich', 'Seville', 'Milan', 'Stockholm', 'Tallinn']
    durations = {
        'Bucharest': 4,
        'Munich': 5,
        'Seville': 5,
        'Milan': 2,
        'Stockholm': 5,
        'Tallinn': 2
    }
    events = {
        'Bucharest': (1, 4),
        'Munich': (4, 8),
        'Seville': (8, 12)
    }
    graph = {
        'Milan': ['Stockholm', 'Munich', 'Seville'],
        'Munich': ['Milan', 'Stockholm', 'Bucharest', 'Seville', 'Tallinn'],
        'Bucharest': ['Munich'],
        'Seville': ['Munich', 'Milan'],
        'Stockholm': ['Milan', 'Munich', 'Tallinn'],
        'Tallinn': ['Stockholm', 'Munich']
    }
    
    for perm in itertools.permutations(cities):
        valid_path = True
        for i in range(len(perm)-1):
            if perm[i+1] not in graph[perm[i]]:
                valid_path = False
                break
        if not valid_path:
            continue
            
        starts = [0] * len(perm)
        ends = [0] * len(perm)
        starts[0] = 1
        ends[0] = starts[0] + durations[perm[0]] - 1
        for i in range(1, len(perm)):
            starts[i] = ends[i-1]
            ends[i] = starts[i] + durations[perm[i]] - 1
        
        if ends[-1] > 18:
            continue
            
        event_ok = True
        for city, (low, high) in events.items():
            if city in perm:
                idx = perm.index(city)
                s = starts[idx]
                e = ends[idx]
                if not (s <= high and e >= low):
                    event_ok = False
                    break
            else:
                event_ok = False
                break
                
        if not event_ok:
            continue
            
        itinerary_list = []
        for i in range(len(perm)):
            s = starts[i]
            e = ends[i]
            if s == e:
                day_range_str = f"Day {s}"
            else:
                day_range_str = f"Day {s}-{e}"
            itinerary_list.append({"day_range": day_range_str, "place": perm[i]})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
        return
    
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()