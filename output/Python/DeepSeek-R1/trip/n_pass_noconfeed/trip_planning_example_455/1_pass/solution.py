import itertools
import json

def main():
    req_dict = {
        'Reykjavik': 7,
        'Riga': 2,
        'Warsaw': 3,
        'Istanbul': 6,
        'Krakow': 7
    }
    
    graph = {
        'Riga': ['Istanbul', 'Warsaw'],
        'Istanbul': ['Krakow', 'Warsaw', 'Riga'],
        'Warsaw': ['Reykjavik', 'Istanbul', 'Krakow', 'Riga'],
        'Reykjavik': ['Warsaw'],
        'Krakow': ['Istanbul', 'Warsaw']
    }
    
    cities = ['Reykjavik', 'Warsaw', 'Istanbul', 'Krakow']
    found = False
    result_itinerary = None
    
    for perm in itertools.permutations(cities):
        c1, c2, c3, c4 = perm
        
        if c1 not in graph['Riga']:
            continue
        if c2 not in graph.get(c1, []):
            continue
        if c3 not in graph.get(c2, []):
            continue
        if c4 not in graph.get(c3, []):
            continue
        
        L1 = req_dict[c1]
        L2 = req_dict[c2]
        L3 = req_dict[c3]
        L4 = 23 - (L1 + L2 + L3)
        
        if L4 != req_dict[c4]:
            continue
        
        d1 = L1 + 1
        d2 = L1 + L2
        d3 = L1 + L2 + L3 - 1
        
        if d3 > 21:
            continue
        
        if c1 == 'Istanbul':
            pass
        elif c2 == 'Istanbul':
            if c1 != 'Warsaw':
                continue
        else:
            continue
        
        itinerary = [
            {"day_range": "Day 1-2", "place": "Riga"},
            {"day_range": f"Day 2-{d1}", "place": c1},
            {"day_range": f"Day {d1}-{d2}", "place": c2},
            {"day_range": f"Day {d2}-{d3}", "place": c3},
            {"day_range": f"Day {d3}-21", "place": c4}
        ]
        found = True
        result_itinerary = itinerary
        break
    
    if not found:
        result_itinerary = []
    
    print(json.dumps({"itinerary": result_itinerary}))

if __name__ == '__main__':
    main()