import itertools
import json

def main():
    cities = ["Split", "Helsinki", "Reykjavik", "Vilnius", "Geneva"]
    days_req = {
        "Split": 2,
        "Helsinki": 2,
        "Reykjavik": 3,
        "Vilnius": 3,
        "Geneva": 6
    }
    
    connections = [
        ("Split", "Helsinki"),
        ("Geneva", "Split"),
        ("Geneva", "Helsinki"),
        ("Helsinki", "Reykjavik"),
        ("Vilnius", "Helsinki"),
        ("Split", "Vilnius")
    ]
    
    edges = set()
    for a, b in connections:
        edges.add((a, b))
        edges.add((b, a))
    
    found = False
    result_itinerary = None
    
    for perm in itertools.permutations(cities):
        valid_connection = True
        for i in range(4):
            if (perm[i], perm[i+1]) not in edges:
                valid_connection = False
                break
        if not valid_connection:
            continue
            
        d0 = days_req[perm[0]]
        d1 = days_req[perm[1]]
        d2 = days_req[perm[2]]
        d3 = days_req[perm[3]]
        d4 = days_req[perm[4]]
        
        e0 = d0
        e1 = d0 + d1 - 1
        e2 = d0 + d1 + d2 - 2
        e3 = d0 + d1 + d2 + d3 - 3
        
        if e0 < 1 or e0 > 12 or e1 > 12 or e2 > 12 or e3 > 12:
            continue
            
        last_city_days = 12 - e3 + 1
        if last_city_days != d4:
            continue
            
        idx_reyk = perm.index("Reykjavik")
        if idx_reyk == 0:
            start_reyk, end_reyk = 1, e0
        elif idx_reyk == 1:
            start_reyk, end_reyk = e0, e1
        elif idx_reyk == 2:
            start_reyk, end_reyk = e1, e2
        elif idx_reyk == 3:
            start_reyk, end_reyk = e2, e3
        else:
            start_reyk, end_reyk = e3, 12
            
        if not (start_reyk <= 12 and end_reyk >= 10):
            continue
            
        idx_vil = perm.index("Vilnius")
        if idx_vil == 0:
            start_vil, end_vil = 1, e0
        elif idx_vil == 1:
            start_vil, end_vil = e0, e1
        elif idx_vil == 2:
            start_vil, end_vil = e1, e2
        elif idx_vil == 3:
            start_vil, end_vil = e2, e3
        else:
            start_vil, end_vil = e3, 12
            
        if not (start_vil <= 9 and end_vil >= 7):
            continue
            
        itinerary = []
        itinerary.append({"day_range": f"Day 1-{e0}", "place": perm[0]})
        itinerary.append({"day_range": f"Day {e0}-{e1}", "place": perm[1]})
        itinerary.append({"day_range": f"Day {e1}-{e2}", "place": perm[2]})
        itinerary.append({"day_range": f"Day {e2}-{e3}", "place": perm[3]})
        itinerary.append({"day_range": f"Day {e3}-12", "place": perm[4]})
        
        found = True
        result_itinerary = itinerary
        break
        
    if not found:
        result = {"itinerary": []}
    else:
        result = {"itinerary": result_itinerary}
        
    print(json.dumps(result))
    
if __name__ == '__main__':
    main()