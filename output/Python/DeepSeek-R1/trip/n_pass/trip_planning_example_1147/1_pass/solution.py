import itertools
import json

def main():
    intermediates = {
        "Brussels": 3,
        "Helsinki": 3,
        "Split": 4,
        "Dubrovnik": 2,
        "Milan": 4
    }
    
    graph = {
        "Istanbul": {"Brussels", "Helsinki", "Milan", "Dubrovnik", "Frankfurt", "Vilnius"},
        "Brussels": {"Istanbul", "Helsinki", "Milan", "Frankfurt", "Vilnius"},
        "Helsinki": {"Istanbul", "Brussels", "Split", "Dubrovnik", "Milan", "Frankfurt", "Vilnius"},
        "Milan": {"Istanbul", "Brussels", "Helsinki", "Split", "Frankfurt", "Vilnius"},
        "Split": {"Helsinki", "Milan", "Frankfurt", "Vilnius"},
        "Dubrovnik": {"Istanbul", "Helsinki", "Frankfurt"},
        "Frankfurt": {"Istanbul", "Brussels", "Helsinki", "Milan", "Split", "Dubrovnik", "Vilnius"},
        "Vilnius": {"Istanbul", "Brussels", "Helsinki", "Milan", "Split", "Frankfurt"}
    }
    
    cities = list(intermediates.keys())
    found_order = None
    
    for perm in itertools.permutations(cities):
        valid = True
        if perm[0] not in graph["Istanbul"]:
            valid = False
        if perm[-1] not in graph["Frankfurt"]:
            valid = False
        if not valid:
            continue
        
        for i in range(len(perm)-1):
            if perm[i+1] not in graph[perm[i]]:
                valid = False
                break
        if not valid:
            continue
        
        current = 5
        for city in perm:
            duration = intermediates[city]
            end_day = current + duration - 1
            current = end_day
        if end_day == 16:
            found_order = perm
            break
    
    if found_order is None:
        print(json.dumps({"itinerary": []}))
        return
    
    itinerary = []
    itinerary.append({"day_range": "Day 1-5", "place": "Istanbul"})
    
    current_day = 5
    for city in found_order:
        duration = intermediates[city]
        end_day = current_day + duration - 1
        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": city})
        current_day = end_day
    
    itinerary.append({"day_range": "Day 16-18", "place": "Frankfurt"})
    itinerary.append({"day_range": "Day 18-22", "place": "Vilnius"})
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()