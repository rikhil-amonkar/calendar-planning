import json
from collections import defaultdict

def main():
    # Define city durations
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
    
    # Define direct flight connections (undirected graph)
    edges = [
        ("Warsaw", "Reykjavik"),
        ("Oslo", "Madrid"),
        ("Warsaw", "Riga"),
        ("Lyon", "London"),
        ("Madrid", "London"),
        ("Warsaw", "London"),
        ("Reykjavik", "Madrid"),
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
    
    # Build graph
    graph = defaultdict(set)
    for a, b in edges:
        graph[a].add(b)
        graph[b].add(a)
    
    # DFS to find valid itinerary
    def dfs(path, rem, cum_dur):
        if not rem:
            return path
        k = len(path)
        last = path[-1] if path else None
        for city in list(rem):
            if last is None or city in graph[last]:
                start_day = 1 + cum_dur - k
                if city == "Riga" and start_day not in [3,4,5]:
                    continue
                if city == "Dubrovnik" and start_day not in [6,7,8]:
                    continue
                new_rem = rem - {city}
                new_cum_dur = cum_dur + durations[city]
                new_path = path + [city]
                result = dfs(new_path, new_rem, new_cum_dur)
                if result is not None:
                    return result
        return None
    
    cities_set = set(durations.keys())
    solution = dfs([], cities_set, 0)
    
    if solution is None:
        print(json.dumps({"itinerary": []}))
        return
    
    # Calculate start days
    starts = []
    starts.append(1)
    for i in range(1, len(solution)):
        starts.append(starts[i-1] + durations[solution[i-1]] - 1)
    
    # Build itinerary
    itinerary_list = []
    for i, city in enumerate(solution):
        start = starts[i]
        end = start + durations[city] - 1
        day_range = f"Day {start}-{end}" if start != end else f"Day {start}"
        itinerary_list.append({"day_range": day_range, "place": city})
    
    print(json.dumps({"itinerary": itinerary_list}))

if __name__ == "__main__":
    main()