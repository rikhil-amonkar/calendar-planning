import itertools
import json

def main():
    graph = {
        'C': ['Vi', 'N', 'Sp', 'S', 'Ve', 'P', 'R'],
        'N': ['S', 'R', 'P', 'Ve', 'Vi', 'C'],
        'Sp': ['C', 'S', 'Vi'],
        'R': ['N', 'Vi', 'C', 'S'],
        'S': ['N', 'C', 'Vi', 'Sp', 'R'],
        'Ve': ['N', 'Vi', 'C'],
        'Vi': ['C', 'R', 'N', 'S', 'Ve', 'Sp', 'P'],
        'P': ['N', 'C', 'Vi']
    }
    
    durations = {
        'R': 2,
        'S': 2,
        'P': 5,
        'N': 3,
        'Ve': 4,
        'Vi': 3,
        'Sp': 3,
        'C': 2
    }
    
    constraints = {
        'R': (2, 4),
        'S': (3, 5),
        'Vi': (9, 13),
        'P': (9, 13)
    }
    
    city_names = {
        'R': "Reykjavik",
        'S': "Stockholm",
        'P': "Porto",
        'N': "Nice",
        'Ve': "Venice",
        'Vi': "Vienna",
        'Sp': "Split",
        'C': "Copenhagen"
    }
    
    cities = list(durations.keys())
    for perm in itertools.permutations(cities):
        valid = True
        for i in range(len(perm)-1):
            if perm[i+1] not in graph[perm[i]]:
                valid = False
                break
        if not valid:
            continue
            
        starts = [1]
        for i in range(1, len(perm)):
            next_start = starts[i-1] + durations[perm[i-1]] - 1
            starts.append(next_start)
        
        constraint_met = True
        for i, city in enumerate(perm):
            if city in constraints:
                low, high = constraints[city]
                if starts[i] < low or starts[i] > high:
                    constraint_met = False
                    break
                    
        if constraint_met:
            itinerary_list = []
            for idx, city_key in enumerate(perm):
                start = starts[idx]
                end = start + durations[city_key] - 1
                if start == end:
                    day_range_str = f"Day {start}"
                else:
                    day_range_str = f"Day {start}-{end}"
                itinerary_list.append({
                    "day_range": day_range_str,
                    "place": city_names[city_key]
                })
            result = {"itinerary": itinerary_list}
            print(json.dumps(result))
            return
            
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()