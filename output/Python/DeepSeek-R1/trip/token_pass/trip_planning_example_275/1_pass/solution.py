import json
from itertools import permutations

def main():
    total_days = 14
    city_days = {
        "Split": 5,
        "Vilnius": 4,
        "Santorini": 2,
        "Madrid": 6
    }
    fixed_days = {"Santorini": (13, 14)}
    graph = {
        "Vilnius": ["Split"],
        "Split": ["Vilnius", "Madrid"],
        "Madrid": ["Split", "Santorini"],
        "Santorini": ["Madrid"]
    }
    
    cities = list(city_days.keys())
    valid_paths = []
    
    for path in permutations(cities):
        if path[-1] != 'Santorini':
            continue
        valid = True
        for i in range(len(path)-1):
            if path[i+1] not in graph[path[i]]:
                valid = False
                break
        if valid:
            valid_paths.append(path)
    
    itinerary = []
    for path in valid_paths:
        d1 = city_days[path[0]]
        d2 = d1 + city_days[path[1]] - 1
        d3 = d2 + city_days[path[2]] - 1
        if 14 - d3 + 1 == city_days[path[3]] and d3 <= 14:
            itinerary = [
                {"day_range": f"Day 1-{d1}", "place": path[0]},
                {"day_range": f"Day {d1}-{d2}", "place": path[1]},
                {"day_range": f"Day {d2}-{d3}", "place": path[2]},
                {"day_range": f"Day {d3}-14", "place": path[3]}
            ]
            break
    
    if not itinerary:
        print("No valid itinerary found")
        return
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()