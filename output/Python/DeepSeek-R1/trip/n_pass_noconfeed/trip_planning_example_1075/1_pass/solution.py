import itertools
import json

def main():
    cities = ["Vienna", "Lyon", "Edinburgh", "Reykjavik", "Stuttgart", "Manchester", "Split", "Prague"]
    
    days_map = {
        "Vienna": 4,
        "Lyon": 3,
        "Edinburgh": 4,
        "Reykjavik": 5,
        "Stuttgart": 5,
        "Manchester": 2,
        "Split": 5,
        "Prague": 4
    }
    
    graph = {city: [] for city in cities}
    
    graph["Reykjavik"].append("Stuttgart")
    graph["Manchester"].append("Split")
    
    bidirectional_pairs = [
        ("Stuttgart", "Split"),
        ("Stuttgart", "Vienna"),
        ("Prague", "Manchester"),
        ("Edinburgh", "Prague"),
        ("Prague", "Vienna"),
        ("Vienna", "Manchester"),
        ("Prague", "Split"),
        ("Vienna", "Lyon"),
        ("Stuttgart", "Edinburgh"),
        ("Split", "Lyon"),
        ("Stuttgart", "Manchester"),
        ("Prague", "Lyon"),
        ("Reykjavik", "Vienna"),
        ("Prague", "Reykjavik"),
        ("Vienna", "Split")
    ]
    
    for a, b in bidirectional_pairs:
        graph[a].append(b)
        graph[b].append(a)
    
    for perm in itertools.permutations(cities):
        s = [0] * 8
        e = [0] * 8
        
        s[0] = 1
        e[0] = s[0] + days_map[perm[0]] - 1
        
        for i in range(1, 8):
            s[i] = e[i-1]
            e[i] = s[i] + days_map[perm[i]] - 1
        
        valid = True
        for i in range(7):
            from_city = perm[i]
            to_city = perm[i+1]
            if to_city not in graph[from_city]:
                valid = False
                break
        
        if not valid:
            continue
        
        edinburgh_index = None
        split_index = None
        for idx, city in enumerate(perm):
            if city == "Edinburgh":
                edinburgh_index = idx
            if city == "Split":
                split_index = idx
        
        if edinburgh_index is None or split_index is None:
            continue
        
        if s[edinburgh_index] > 5 or e[edinburgh_index] < 8:
            continue
        
        if s[split_index] > 23 or e[split_index] < 19:
            continue
        
        itinerary_list = []
        for i in range(8):
            start = s[i]
            end = e[i]
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary_list.append({
                "day_range": day_range_str,
                "place": perm[i]
            })
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
        return
    
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()