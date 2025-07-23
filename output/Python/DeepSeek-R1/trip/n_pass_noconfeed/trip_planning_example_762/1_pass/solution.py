import itertools
import json

def main():
    cities = ['Berlin', 'Dublin', 'Madrid', 'Oslo', 'London', 'Vilnius']
    days_req = {
        'Berlin': 5,
        'Dublin': 3,
        'Madrid': 2,
        'Oslo': 3,
        'London': 2,
        'Vilnius': 3
    }
    
    edges_list = [
        ('London', 'Madrid'),
        ('Oslo', 'Vilnius'),
        ('Berlin', 'Vilnius'),
        ('Madrid', 'Oslo'),
        ('Madrid', 'Dublin'),
        ('London', 'Oslo'),
        ('Madrid', 'Berlin'),
        ('Berlin', 'Oslo'),
        ('Dublin', 'Oslo'),
        ('London', 'Dublin'),
        ('London', 'Berlin'),
        ('Berlin', 'Dublin')
    ]
    
    graph_edges = set()
    for a, b in edges_list:
        key = tuple(sorted([a, b]))
        graph_edges.add(key)
    
    perms = list(itertools.permutations(cities))
    found_itinerary = None
    
    for perm in perms:
        valid_flight = True
        for i in range(len(perm) - 1):
            a, b = perm[i], perm[i+1]
            key = tuple(sorted([a, b]))
            if key not in graph_edges:
                valid_flight = False
                break
        if not valid_flight:
            continue
            
        starts = [1]
        for idx in range(1, len(perm)):
            prev_city = perm[idx-1]
            prev_days = days_req[prev_city]
            start_i = starts[-1] + prev_days - 1
            starts.append(start_i)
            
        blocks = []
        for idx, city in enumerate(perm):
            s = starts[idx]
            e = s + days_req[city] - 1
            blocks.append((s, e, city))
            
        valid_constraints = True
        for s, e, city in blocks:
            if city == 'Madrid':
                if s not in [1, 2, 3]:
                    valid_constraints = False
                    break
            elif city == 'Berlin':
                if s > 7:
                    valid_constraints = False
                    break
            elif city == 'Dublin':
                if s < 5 or s > 9:
                    valid_constraints = False
                    break
                    
        if valid_constraints:
            found_itinerary = blocks
            break
            
    if found_itinerary is None:
        result = {"itinerary": []}
    else:
        itinerary_list = []
        for s, e, city in found_itinerary:
            if s == e:
                day_range_str = f"Day {s}"
            else:
                day_range_str = f"Day {s}-{e}"
            itinerary_list.append({"day_range": day_range_str, "place": city})
        result = {"itinerary": itinerary_list}
        
    print(json.dumps(result))

if __name__ == "__main__":
    main()