import json
import itertools

def main():
    graph = {
        'London': ['Copenhagen', 'Mykonos', 'Nice', 'Oslo'],
        'Copenhagen': ['London', 'Tallinn', 'Nice', 'Oslo'],
        'Tallinn': ['Copenhagen', 'Oslo'],
        'Mykonos': ['London', 'Nice'],
        'Oslo': ['Tallinn', 'Nice', 'London', 'Copenhagen'],
        'Nice': ['Oslo', 'London', 'Mykonos', 'Copenhagen']
    }
    
    durations = {
        'Mykonos': 4,
        'London': 2,
        'Copenhagen': 3,
        'Tallinn': 4,
        'Oslo': 5
    }
    
    cities = ['Mykonos', 'London', 'Copenhagen', 'Tallinn', 'Oslo']
    found = False
    valid_perm = None
    
    for perm in itertools.permutations(cities):
        valid_flight = True
        for i in range(len(perm)-1):
            if perm[i+1] not in graph[perm[i]]:
                valid_flight = False
                break
        if not valid_flight:
            continue
            
        if 'Nice' not in graph[perm[4]]:
            continue
            
        try:
            k = perm.index('Oslo')
        except ValueError:
            continue
            
        if k == 0:
            start_oslo = 1
        elif k == 1:
            start_oslo = durations[perm[0]]
        elif k == 2:
            start_oslo = durations[perm[0]] + durations[perm[1]] - 1
        elif k == 3:
            start_oslo = durations[perm[0]] + durations[perm[1]] + durations[perm[2]] - 2
        elif k == 4:
            start_oslo = durations[perm[0]] + durations[perm[1]] + durations[perm[2]] + durations[perm[3]] - 3
            
        if start_oslo < 6 or start_oslo > 14:
            continue
            
        found = True
        valid_perm = perm
        break
        
    if not found:
        print(json.dumps({"itinerary": []}))
        return
        
    starts = [0] * 5
    ends = [0] * 5
    starts[0] = 1
    ends[0] = starts[0] + durations[valid_perm[0]] - 1
    
    for i in range(1, 5):
        starts[i] = ends[i-1]
        ends[i] = starts[i] + durations[valid_perm[i]] - 1
        
    itinerary_list = []
    for i in range(5):
        s = starts[i]
        e = ends[i]
        if s == e:
            day_range_str = f"Day {s}"
        else:
            day_range_str = f"Day {s}-{e}"
        itinerary_list.append({"day_range": day_range_str, "place": valid_perm[i]})
        
    itinerary_list.append({"day_range": "Day 14-16", "place": "Nice"})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))
    
if __name__ == "__main__":
    main()