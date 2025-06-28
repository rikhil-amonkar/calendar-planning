import itertools
import json

def main():
    cities = ['Reykjavik', 'Stockholm', 'Porto', 'Nice', 'Venice', 'Vienna', 'Split', 'Copenhagen']
    
    durations = {
        'Reykjavik': 2,
        'Stockholm': 2,
        'Porto': 5,
        'Nice': 3,
        'Venice': 4,
        'Vienna': 3,
        'Split': 3,
        'Copenhagen': 2
    }
    
    edges = [
        "Copenhagen and Vienna",
        "Nice and Stockholm",
        "Split and Copenhagen",
        "Nice and Reykjavik",
        "Nice and Porto",
        "Reykjavik and Vienna",
        "Stockholm and Copenhagen",
        "Nice and Venice",
        "Nice and Vienna",
        "Reykjavik and Copenhagen",
        "Nice and Copenhagen",
        "Stockholm and Vienna",
        "Venice and Vienna",
        "Copenhagen and Porto",
        "Reykjavik and Stockholm",
        "Stockholm and Split",
        "Split and Vienna",
        "Copenhagen and Venice",
        "Vienna and Porto"
    ]
    
    graph = {}
    for edge in edges:
        a, b = edge.split(' and ')
        if a not in graph:
            graph[a] = set()
        if b not in graph:
            graph[b] = set()
        graph[a].add(b)
        graph[b].add(a)
    
    valid_permutation = None
    valid_starts = None
    
    for perm in itertools.permutations(cities):
        valid_flight = True
        for i in range(len(perm)-1):
            if perm[i+1] not in graph.get(perm[i], set()):
                valid_flight = False
                break
        if not valid_flight:
            continue
        
        s = [0] * 8
        s[0] = 1
        for i in range(1, 8):
            s[i] = s[i-1] + durations[perm[i-1]] - 1
        
        rey_start = None
        stock_start = None
        vienna_start = None
        porto_start = None
        
        for i in range(8):
            city = perm[i]
            if city == 'Reykjavik':
                rey_start = s[i]
            elif city == 'Stockholm':
                stock_start = s[i]
            elif city == 'Vienna':
                vienna_start = s[i]
            elif city == 'Porto':
                porto_start = s[i]
        
        if rey_start is not None and not (2 <= rey_start <= 4):
            continue
        if stock_start is not None and not (3 <= stock_start <= 5):
            continue
        if vienna_start is not None and not (9 <= vienna_start <= 13):
            continue
        if porto_start is not None and not (9 <= porto_start <= 13):
            continue
        
        valid_permutation = perm
        valid_starts = s
        break
    
    if valid_permutation is None:
        print(json.dumps({"itinerary": []}))
    else:
        itinerary_list = []
        for i, city in enumerate(valid_permutation):
            start_day = valid_starts[i]
            end_day = start_day + durations[city] - 1
            day_range_str = f"Day {start_day}-{end_day}"
            itinerary_list.append({"day_range": day_range_str, "place": city})
        print(json.dumps({"itinerary": itinerary_list}))

if __name__ == "__main__":
    main()