import itertools
import json

def main():
    cities = ["Amsterdam", "Vienna", "Santorini", "Lyon"]
    durations = {
        "Amsterdam": 3,
        "Vienna": 7,
        "Santorini": 4,
        "Lyon": 3
    }
    
    flight_pairs = [
        ("Vienna", "Lyon"),
        ("Vienna", "Santorini"),
        ("Vienna", "Amsterdam"),
        ("Amsterdam", "Santorini"),
        ("Amsterdam", "Lyon")
    ]
    
    flight_set = set()
    for a, b in flight_pairs:
        flight_set.add((a, b))
        flight_set.add((b, a))
    
    valid_perm = None
    for perm in itertools.permutations(cities):
        if (perm[0], perm[1]) not in flight_set:
            continue
        if (perm[1], perm[2]) not in flight_set:
            continue
        if (perm[2], perm[3]) not in flight_set:
            continue
        
        d1 = durations[perm[0]]
        d2 = durations[perm[1]]
        d3 = durations[perm[2]]
        d4 = durations[perm[3]]
        
        E1 = d1
        E2 = d1 + d2 - 1
        E3 = 15 - d4
        
        idx_amsterdam = perm.index('Amsterdam')
        idx_lyon = perm.index('Lyon')
        
        if idx_amsterdam == 0:
            cond_amsterdam = (E1 >= 9)
        elif idx_amsterdam == 1:
            cond_amsterdam = (E1 <= 11 and E2 >= 9)
        elif idx_amsterdam == 2:
            cond_amsterdam = (E2 <= 11 and E3 >= 9)
        else:
            cond_amsterdam = (E3 <= 11)
        
        if idx_lyon == 0:
            cond_lyon = (E1 >= 7)
        elif idx_lyon == 1:
            cond_lyon = (E1 <= 9 and E2 >= 7)
        elif idx_lyon == 2:
            cond_lyon = (E2 <= 9 and E3 >= 7)
        else:
            cond_lyon = (E3 <= 9)
        
        if cond_amsterdam and cond_lyon:
            valid_perm = perm
            break
    
    if valid_perm:
        d1 = durations[valid_perm[0]]
        d2 = durations[valid_perm[1]]
        d4 = durations[valid_perm[3]]
        E1 = d1
        E2 = d1 + d2 - 1
        E3 = 15 - d4
        
        itinerary = [
            {"day_range": f"Day 1-{E1}", "place": valid_perm[0]},
            {"day_range": f"Day {E1}-{E2}", "place": valid_perm[1]},
            {"day_range": f"Day {E2}-{E3}", "place": valid_perm[2]},
            {"day_range": f"Day {E3}-14", "place": valid_perm[3]}
        ]
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()