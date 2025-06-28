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
    
    cities_set = set(durations.keys())
    cities_set.discard("Warsaw")
    
    best_path = None
    best_num_cities = -1
    
    def dfs(path, remaining, current_day, total_days):
        nonlocal best_path, best_num_cities
        
        if total_days > 18:
            return
        
        if not remaining or total_days == 18:
            num_cities = len(path) - 1
            if num_cities > best_num_cities and total_days == 18:
                best_path = path[:]
                best_num_cities = num_cities
            return
        
        last_city = path[-1] if path else "Warsaw"
        
        for next_city in list(remaining):
            if next_city not in graph[last_city]:
                continue
                
            start_day = current_day
            if next_city == "Riga" and start_day not in [3, 4, 5]:
                continue
            if next_city == "Dubrovnik" and start_day not in [6, 7, 8]:
                continue
                
            stay_duration = durations[next_city]
            end_day = start_day + stay_duration - 1
            if end_day > 18:
                continue
                
            next_remaining = remaining - {next_city}
            next_current_day = end_day + 2
            next_total_days = total_days + stay_duration + 1
            
            dfs(path + [next_city], next_remaining, next_current_day, next_total_days)
    
    dfs(["Warsaw"], cities_set, 1 + durations["Warsaw"], durations["Warsaw"])
    
    if best_path is None:
        print(json.dumps({"itinerary": []}))
        return
    
    starts = [1]
    for i in range(1, len(best_path)):
        starts.append(starts[i-1] + durations[best_path[i-1]] + 1)
    
    itinerary_list = []
    for i, city in enumerate(best_path):
        start = starts[i]
        end = start + durations[city] - 1
        day_range = f"Day {start}-{end}" if start != end else f"Day {start}"
        itinerary_list.append({"day_range": day_range, "place": city})
    
    print(json.dumps({"itinerary": itinerary_list}))

if __name__ == "__main__":
    main()