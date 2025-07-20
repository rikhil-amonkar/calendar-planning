import itertools
import json

def main():
    city_duration = {
        "Geneva": 4,
        "Istanbul": 4,
        "Vienna": 4,
        "Riga": 2,
        "Brussels": 2,
        "Madrid": 4,
        "Vilnius": 4,
        "Venice": 5,
        "Munich": 5,
        "Reykjavik": 2
    }
    
    edges = [
        ("Munich", "Vienna"),
        ("Istanbul", "Brussels"),
        ("Vienna", "Vilnius"),
        ("Madrid", "Munich"),
        ("Venice", "Brussels"),
        ("Riga", "Brussels"),
        ("Geneva", "Istanbul"),
        ("Munich", "Reykjavik"),
        ("Vienna", "Istanbul"),
        ("Riga", "Istanbul"),
        ("Reykjavik", "Vienna"),
        ("Venice", "Munich"),
        ("Madrid", "Venice"),
        ("Vilnius", "Istanbul"),
        ("Venice", "Vienna"),
        ("Venice", "Istanbul"),
        ("Reykjavik", "Madrid"),
        ("Riga", "Munich"),
        ("Munich", "Istanbul"),
        ("Reykjavik", "Brussels"),
        ("Vilnius", "Brussels"),
        ("Vilnius", "Munich"),
        ("Madrid", "Vienna"),
        ("Vienna", "Riga"),
        ("Geneva", "Vienna"),
        ("Geneva", "Brussels"),
        ("Geneva", "Madrid"),
        ("Madrid", "Brussels"),
        ("Vienna", "Brussels"),
        ("Munich", "Brussels"),
        ("Madrid", "Istanbul"),
        ("Geneva", "Munich"),
        ("Riga", "Vilnius")
    ]
    
    graph = {}
    for a, b in edges:
        if a not in graph:
            graph[a] = set()
        if b not in graph:
            graph[b] = set()
        graph[a].add(b)
        graph[b].add(a)
    
    start_city = "Geneva"
    end_city = "Brussels"
    other_cities = ["Istanbul", "Vienna", "Riga", "Madrid", "Vilnius", "Venice", "Munich", "Reykjavik"]
    
    for perm in itertools.permutations(other_cities):
        sequence = [start_city] + list(perm) + [end_city]
        valid_sequence = True
        for i in range(len(sequence) - 1):
            a = sequence[i]
            b = sequence[i+1]
            if a not in graph or b not in graph[a]:
                valid_sequence = False
                break
        if not valid_sequence:
            continue
        
        starts = [1]
        for i in range(1, 10):
            prev_city = sequence[i-1]
            starts.append(starts[i-1] + city_duration[prev_city] - 1)
        
        if starts[9] + city_duration["Brussels"] - 1 != 27:
            continue
        
        venice_index = None
        vilnius_index = None
        for idx, city in enumerate(sequence):
            if city == "Venice":
                venice_index = idx
            if city == "Vilnius":
                vilnius_index = idx
        
        if venice_index is None or vilnius_index is None:
            continue
        
        s_venice = starts[venice_index]
        if not (s_venice <= 11 and s_venice + 4 >= 7):
            continue
        
        s_vilnius = starts[vilnius_index]
        if not (s_vilnius <= 23 and s_vilnius + 3 >= 20):
            continue
        
        itinerary = []
        for i in range(10):
            city_name = sequence[i]
            start_day = starts[i]
            end_day = start_day + city_duration[city_name] - 1
            day_range_str = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range_str, "place": city_name})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
        return
    
    print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()