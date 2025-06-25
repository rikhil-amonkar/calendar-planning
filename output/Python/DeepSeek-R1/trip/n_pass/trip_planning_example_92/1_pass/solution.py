import itertools
import json

def main():
    total_days = 12
    city_days = {
        'Riga': 5,
        'Vilnius': 7,
        'Dublin': 2
    }
    direct_flights = [('Dublin', 'Riga'), ('Riga', 'Vilnius')]
    
    graph = {}
    for (u, v) in direct_flights:
        if u not in graph:
            graph[u] = set()
        graph[u].add(v)
        if v not in graph:
            graph[v] = set()
        graph[v].add(u)
    
    cities_list = list(city_days.keys())
    valid_paths = []
    for perm in itertools.permutations(cities_list):
        valid = True
        n = len(perm)
        for i in range(n-1):
            u = perm[i]
            v = perm[i+1]
            if u in graph and v in graph[u]:
                continue
            else:
                valid = False
                break
        if valid:
            valid_paths.append(perm)
    
    if not valid_paths:
        result = {"itinerary": []}
    else:
        valid_paths.sort(key=lambda path: city_days[path[0]])
        chosen_path = valid_paths[0]
        
        current_start = 1
        itinerary_list = []
        for city in chosen_path:
            d = city_days[city]
            end = current_start + d - 1
            itinerary_list.append({
                "day_range": f"Day {current_start}-{end}",
                "place": city
            })
            current_start = end
        
        if end != total_days:
            result = {"itinerary": []}
        else:
            result = {"itinerary": itinerary_list}
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()