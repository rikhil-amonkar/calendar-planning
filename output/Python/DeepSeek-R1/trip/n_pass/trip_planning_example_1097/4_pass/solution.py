import json
from collections import defaultdict

def main():
    durations = {
        "Reykjavik": 4,
        "Riga": 2,
        "Oslo": 3,
        "Lyon": 5,
        "Dubrovnik": 2,
        "Madrid": 2,
        "Warsaw": 4,
        "London": 3
    }
    
    edges = [
        ("Warsaw", "Reykjavik"),
        ("Oslo", "Madrid"),
        ("Warsaw", "Riga"),
        ("Lyon", "London"),
        ("Madrid", "London"),
        ("Warsaw", "London"),
        ("Warsaw", "Oslo"),
        ("Oslo", "Dubrovnik"),
        ("Oslo", "Reykjavik"),
        ("Riga", "Oslo"),
        ("Oslo", "Lyon"),
        ("Oslo", "London"),
        ("London", "Reykjavik"),
        ("Warsaw", "Madrid"),
        ("Madrid", "Lyon"),
        ("Dubrovnik", "Madrid")
    ]
    
    graph = defaultdict(set)
    for a, b in edges:
        graph[a].add(b)
        graph[b].add(a)
    
    cities = set(durations.keys())
    remaining = cities - {"Warsaw", "Reykjavik"}
    
    best_path = None
    best_num_cities = -1
    
    def dfs(path, remaining, current_day):
        nonlocal best_path, best_num_cities
        
        last_city = path[-1]
        # Check if we can add Reykjavik from the last city
        if "Reykjavik" in graph[last_city] and current_day == 15:
            candidate_path = path + ["Reykjavik"]
            num_cities = len(candidate_path)
            if num_cities > best_num_cities:
                best_path = candidate_path
                best_num_cities = num_cities
        
        # If current_day exceeds 14, we can't start any new non-Reykjavik city
        if current_day > 14:
            return
        
        for next_city in list(remaining):
            if next_city not in graph[last_city]:
                continue
                
            # Check specific constraints for Riga and Dubrovnik
            if next_city == "Riga":
                if current_day != 5:
                    continue
            elif next_city == "Dubrovnik":
                if current_day < 6 or current_day > 8:
                    continue
                    
            d = durations[next_city]
            end_day = current_day + d - 1
            if end_day > 14:
                continue
                
            next_start = end_day + 1
            next_remaining = remaining - {next_city}
            dfs(path + [next_city], next_remaining, next_start)
    
    # Start DFS from Warsaw, next available day is 5 (after 4 days in Warsaw)
    dfs(["Warsaw"], remaining, 5)
    
    if best_path is None:
        print(json.dumps({"itinerary": []}))
        return
    
    # Compute start days for each city in the itinerary
    starts = [1]
    for i in range(1, len(best_path)):
        starts.append(starts[i-1] + durations[best_path[i-1]])
    
    itinerary_list = []
    for i, city in enumerate(best_path):
        start = starts[i]
        end = start + durations[city] - 1
        day_range = f"Day {start}-{end}" if start != end else f"Day {start}"
        itinerary_list.append({"day_range": day_range, "place": city})
    
    print(json.dumps({"itinerary": itinerary_list}))

if __name__ == "__main__":
    main()