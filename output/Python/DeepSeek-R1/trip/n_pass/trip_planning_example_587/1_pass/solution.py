import itertools
import json

def main():
    days = {
        "Manchester": 3,
        "Venice": 7,
        "Istanbul": 7,
        "Krakow": 6,
        "Lyon": 2
    }
    
    graph = {
        "Manchester": ["Venice", "Istanbul", "Krakow"],
        "Venice": ["Manchester", "Istanbul", "Lyon"],
        "Istanbul": ["Manchester", "Venice", "Krakow", "Lyon"],
        "Krakow": ["Manchester", "Istanbul"],
        "Lyon": ["Venice", "Istanbul"]
    }
    
    cities = list(days.keys())
    found = False
    itinerary_output = None
    
    for perm in itertools.permutations(cities):
        n = len(perm)
        valid_flight = True
        for i in range(n - 1):
            if perm[i+1] not in graph[perm[i]]:
                valid_flight = False
                break
        if not valid_flight:
            continue
        
        starts = [0] * n
        starts[0] = 1
        for i in range(1, n):
            starts[i] = starts[i-1] + days[perm[i-1]] - 1
        
        idx_man = perm.index("Manchester")
        if starts[idx_man] > 3:
            continue
            
        idx_ven = perm.index("Venice")
        if starts[idx_ven] > 9:
            continue
        
        itinerary_list = []
        for i in range(n):
            start_day = starts[i]
            end_day = start_day + days[perm[i]] - 1
            day_range_str = f"Day {start_day}-{end_day}" if start_day != end_day else f"Day {start_day}"
            itinerary_list.append({"day_range": day_range_str, "place": perm[i]})
        
        found = True
        itinerary_output = itinerary_list
        break
    
    if found:
        result = {"itinerary": itinerary_output}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == '__main__':
    main()