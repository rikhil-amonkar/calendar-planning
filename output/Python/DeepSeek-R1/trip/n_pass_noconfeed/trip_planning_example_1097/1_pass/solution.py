import itertools
import json

def main():
    durations = {
        'Reykjavik': 4,
        'Riga': 2,
        'Oslo': 3,
        'Lyon': 5,
        'Dubrovnik': 2,
        'Madrid': 2,
        'Warsaw': 4,
        'London': 3
    }
    
    graph = {
        'Warsaw': ['Reykjavik', 'Riga', 'London', 'Oslo', 'Madrid'],
        'Reykjavik': ['Warsaw', 'Oslo', 'London', 'Madrid'],
        'Oslo': ['Madrid', 'Warsaw', 'Dubrovnik', 'Reykjavik', 'Riga', 'Lyon', 'London'],
        'Riga': ['Warsaw', 'Oslo'],
        'Lyon': ['London', 'Madrid', 'Oslo'],
        'Madrid': ['Oslo', 'London', 'Warsaw', 'Lyon', 'Dubrovnik'],
        'Dubrovnik': ['Oslo', 'Madrid'],
        'London': ['Lyon', 'Madrid', 'Warsaw', 'Oslo', 'Reykjavik']
    }
    
    cities = list(durations.keys())
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
            
        cumulative = 0
        meets_constraints = True
        for i, city in enumerate(perm):
            start_day = 1 + cumulative - i
            if city == 'Riga':
                if start_day not in [3,4,5]:
                    meets_constraints = False
                    break
            if city == 'Dubrovnik':
                if start_day not in [6,7,8]:
                    meets_constraints = False
                    break
            cumulative += durations[city]
            
        if meets_constraints:
            valid_perm = perm
            found = True
            break
            
    if found:
        itinerary_list = []
        cumulative_sum = 0
        for i, city in enumerate(valid_perm):
            start_day = 1 + cumulative_sum - i
            end_day = start_day + durations[city] - 1
            cumulative_sum += durations[city]
            if start_day == end_day:
                day_range_str = f"Day {start_day}"
            else:
                day_range_str = f"Day {start_day}-{end_day}"
            itinerary_list.append({"day_range": day_range_str, "place": city})
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()