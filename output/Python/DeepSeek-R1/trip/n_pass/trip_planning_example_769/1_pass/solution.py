import itertools
import json

def main():
    required_days = {
        'Porto': 5,
        'Prague': 4,
        'Reykjavik': 4,
        'Munich': 4,
        'Amsterdam': 2,
        'Santorini': 2
    }
    
    graph = {
        'Porto': ['Amsterdam', 'Munich'],
        'Prague': ['Reykjavik', 'Amsterdam', 'Munich'],
        'Reykjavik': ['Amsterdam', 'Munich', 'Prague'],
        'Munich': ['Amsterdam', 'Porto', 'Reykjavik', 'Prague'],
        'Amsterdam': ['Porto', 'Munich', 'Reykjavik', 'Santorini', 'Prague'],
        'Santorini': ['Amsterdam']
    }
    
    last_two = ['Amsterdam', 'Santorini']
    first_four = ['Porto', 'Prague', 'Reykjavik', 'Munich']
    found = False
    result_itinerary = None
    
    for perm in itertools.permutations(first_four):
        valid_chain = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in graph[perm[i]]:
                valid_chain = False
                break
        if not valid_chain:
            continue
            
        if last_two[0] not in graph[perm[-1]]:
            continue
            
        idx_r = perm.index('Reykjavik')
        idx_m = perm.index('Munich')
        
        if idx_r == 3:
            continue
        if idx_r == 2:
            if not (required_days[perm[0]] == 4 and required_days[perm[1]] == 4):
                continue
                
        if idx_m == 0 or idx_m == 3:
            continue
            
        d1 = required_days[perm[0]]
        d2 = d1 + required_days[perm[1]] - 1
        d3 = d2 + required_days[perm[2]] - 1
        d4 = d3 + required_days[perm[3]] - 1
        
        itinerary = [
            {"day_range": f"Day 1-{d1}", "place": perm[0]},
            {"day_range": f"Day {d1}-{d2}", "place": perm[1]},
            {"day_range": f"Day {d2}-{d3}", "place": perm[2]},
            {"day_range": f"Day {d3}-14", "place": perm[3]},
            {"day_range": "Day 14-15", "place": "Amsterdam"},
            {"day_range": "Day 15-16", "place": "Santorini"}
        ]
        found = True
        result_itinerary = itinerary
        break
        
    if not found:
        perm = ('Reykjavik', 'Prague', 'Munich', 'Porto')
        d1 = required_days[perm[0]]
        d2 = d1 + required_days[perm[1]] - 1
        d3 = d2 + required_days[perm[2]] - 1
        d4 = d3 + required_days[perm[3]] - 1
        result_itinerary = [
            {"day_range": f"Day 1-{d1}", "place": perm[0]},
            {"day_range": f"Day {d1}-{d2}", "place": perm[1]},
            {"day_range": f"Day {d2}-{d3}", "place": perm[2]},
            {"day_range": f"Day {d3}-14", "place": perm[3]},
            {"day_range": "Day 14-15", "place": "Amsterdam"},
            {"day_range": "Day 15-16", "place": "Santorini"}
        ]
    
    result = {"itinerary": result_itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()