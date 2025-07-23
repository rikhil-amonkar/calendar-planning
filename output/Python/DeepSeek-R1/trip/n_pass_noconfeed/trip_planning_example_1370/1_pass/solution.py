import itertools
import json

def main():
    durations = {
        'Santorini': 5,
        'Krakow': 5,
        'Paris': 5,
        'Vilnius': 3,
        'Munich': 5,
        'Geneva': 2,
        'Amsterdam': 4,
        'Budapest': 5,
        'Split': 4
    }
    
    graph = {
        'Paris': ['Krakow', 'Amsterdam', 'Split', 'Geneva', 'Budapest', 'Munich', 'Vilnius'],
        'Krakow': ['Paris', 'Split', 'Munich', 'Vilnius', 'Amsterdam'],
        'Amsterdam': ['Paris', 'Geneva', 'Munich', 'Budapest', 'Split', 'Santorini', 'Vilnius', 'Krakow'],
        'Split': ['Paris', 'Geneva', 'Krakow', 'Amsterdam', 'Vilnius', 'Munich'],
        'Vilnius': ['Munich', 'Split', 'Amsterdam', 'Paris'],
        'Geneva': ['Paris', 'Amsterdam', 'Split', 'Munich', 'Budapest', 'Santorini'],
        'Munich': ['Split', 'Amsterdam', 'Geneva', 'Krakow', 'Budapest', 'Paris'],
        'Budapest': ['Amsterdam', 'Paris', 'Geneva', 'Munich'],
        'Santorini': ['Geneva', 'Amsterdam']
    }
    
    cities = list(durations.keys())
    found = False
    result_perm = None
    result_starts = None
    
    for perm in itertools.permutations(cities):
        valid_flight = True
        for i in range(len(perm) - 1):
            from_city = perm[i]
            to_city = perm[i+1]
            if to_city not in graph.get(from_city, []):
                valid_flight = False
                break
        if not valid_flight:
            continue
        
        starts = []
        current_start = 1
        for city in perm:
            starts.append(current_start)
            current_start += durations[city] - 1
        
        valid_constraints = True
        for idx, city in enumerate(perm):
            s = starts[idx]
            e = s + durations[city] - 1
            if city == 'Santorini':
                if not (s <= 29 and e >= 25):
                    valid_constraints = False
                    break
            elif city == 'Krakow':
                if not (s <= 22 and e >= 18):
                    valid_constraints = False
                    break
            elif city == 'Paris':
                if not (s <= 15 and e >= 11):
                    valid_constraints = False
                    break
        
        if valid_constraints:
            found = True
            result_perm = perm
            result_starts = starts
            break
    
    if found:
        itinerary_list = []
        for i in range(len(result_perm)):
            s = result_starts[i]
            e = s + durations[result_perm[i]] - 1
            if s == e:
                day_range = f"Day {s}"
            else:
                day_range = f"Day {s}-{e}"
            itinerary_list.append({
                "day_range": day_range,
                "place": result_perm[i]
            })
        result_json = {"itinerary": itinerary_list}
        print(json.dumps(result_json))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()