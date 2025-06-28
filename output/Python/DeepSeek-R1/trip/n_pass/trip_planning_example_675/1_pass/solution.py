import itertools
import json

def main():
    cities = ['Dubrovnik', 'Split', 'Milan', 'Porto', 'Krakow', 'Munich']
    durations = {
        'Dubrovnik': 4,
        'Split': 3,
        'Milan': 3,
        'Porto': 4,
        'Krakow': 2,
        'Munich': 5
    }
    
    flight_pairs = [
        ('Munich', 'Porto'),
        ('Split', 'Milan'),
        ('Milan', 'Porto'),
        ('Munich', 'Krakow'),
        ('Munich', 'Milan'),
        ('Dubrovnik', 'Munich'),
        ('Krakow', 'Split'),
        ('Krakow', 'Milan'),
        ('Munich', 'Split')
    ]
    
    graph = {}
    for u, v in flight_pairs:
        if u not in graph:
            graph[u] = set()
        graph[u].add(v)
        if v not in graph:
            graph[v] = set()
        graph[v].add(u)
    
    found = False
    result_itinerary = None
    
    for perm in itertools.permutations(cities):
        valid_flight = True
        for i in range(len(perm)-1):
            city1 = perm[i]
            city2 = perm[i+1]
            if city2 not in graph.get(city1, set()):
                valid_flight = False
                break
        if not valid_flight:
            continue
        
        durs = [durations[city] for city in perm]
        starts = [1]
        for i in range(len(perm)-1):
            next_start = starts[i] + durs[i] - 1
            starts.append(next_start)
        ends = [starts[i] + durs[i] - 1 for i in range(len(perm))]
        
        if ends[-1] != 16:
            continue
        
        idx_mu = perm.index('Munich')
        s_mu = starts[idx_mu]
        e_mu = ends[idx_mu]
        if not (s_mu <= 8 and e_mu >= 4):
            continue
        
        idx_k = perm.index('Krakow')
        s_k = starts[idx_k]
        e_k = ends[idx_k]
        if not (s_k <= 9 and e_k >= 8):
            continue
        
        idx_mi = perm.index('Milan')
        s_mi = starts[idx_mi]
        e_mi = ends[idx_mi]
        if not (s_mi <= 13 and e_mi >= 11):
            continue
        
        itinerary_list = []
        for i in range(len(perm)):
            s = starts[i]
            e = ends[i]
            if s == e:
                day_str = f"Day {s}"
            else:
                day_str = f"Day {s}-{e}"
            itinerary_list.append({"day_range": day_str, "place": perm[i]})
        found = True
        result_itinerary = itinerary_list
        break
    
    if found:
        print(json.dumps({"itinerary": result_itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()