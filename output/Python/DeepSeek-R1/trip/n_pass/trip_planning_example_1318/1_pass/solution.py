import itertools
import json

def main():
    durations = {
        'Oslo': 2,
        'Helsinki': 2,
        'Edinburgh': 3,
        'Riga': 2,
        'Tallinn': 5,
        'Budapest': 5,
        'Vilnius': 5,
        'Porto': 5,
        'Geneva': 4
    }
    
    cities = list(durations.keys())
    
    bidirectional_pairs = [
        ('Porto', 'Oslo'),
        ('Edinburgh', 'Budapest'),
        ('Edinburgh', 'Geneva'),
        ('Edinburgh', 'Porto'),
        ('Vilnius', 'Helsinki'),
        ('Riga', 'Oslo'),
        ('Geneva', 'Oslo'),
        ('Edinburgh', 'Oslo'),
        ('Edinburgh', 'Helsinki'),
        ('Vilnius', 'Oslo'),
        ('Riga', 'Helsinki'),
        ('Budapest', 'Geneva'),
        ('Helsinki', 'Budapest'),
        ('Helsinki', 'Oslo'),
        ('Edinburgh', 'Riga'),
        ('Tallinn', 'Helsinki'),
        ('Geneva', 'Porto'),
        ('Budapest', 'Oslo'),
        ('Helsinki', 'Geneva'),
        ('Tallinn', 'Oslo')
    ]
    
    directed_edges = [
        ('Riga', 'Tallinn'),
        ('Tallinn', 'Vilnius'),
        ('Riga', 'Vilnius')
    ]
    
    graph = {city: set() for city in cities}
    for (a, b) in bidirectional_pairs:
        graph[a].add(b)
        graph[b].add(a)
    for (a, b) in directed_edges:
        graph[a].add(b)
    
    found_perm = None
    for perm in itertools.permutations(cities):
        valid_path = True
        for i in range(8):
            if perm[i+1] not in graph[perm[i]]:
                valid_path = False
                break
        if not valid_path:
            continue
            
        if perm[8] == 'Oslo':
            pass
        elif perm[7] == 'Oslo' and perm[8] in ['Helsinki', 'Riga']:
            pass
        else:
            continue
            
        k = perm.index('Tallinn')
        if k == 0:
            found_perm = perm
            break
        else:
            total_prev = sum(durations[perm[j]] for j in range(k))
            S = total_prev - (k - 1)
            if S <= 8:
                found_perm = perm
                break
    
    if found_perm is None:
        print(json.dumps({"itinerary": []}))
        return
    
    starts = [0] * 9
    ends = [0] * 9
    starts[0] = 1
    ends[0] = starts[0] + durations[found_perm[0]] - 1
    for i in range(1, 9):
        starts[i] = ends[i-1]
        ends[i] = starts[i] + durations[found_perm[i]] - 1
    
    itinerary_list = []
    for i in range(9):
        s = starts[i]
        e = ends[i]
        if s == e:
            day_range_str = f"Day {s}"
        else:
            day_range_str = f"Day {s}-{e}"
        itinerary_list.append({
            "day_range": day_range_str,
            "place": found_perm[i]
        })
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()