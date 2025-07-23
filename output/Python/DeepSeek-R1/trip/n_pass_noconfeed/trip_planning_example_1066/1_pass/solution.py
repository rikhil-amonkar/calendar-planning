import itertools
import json

def main():
    days_dict = {
        'Brussels': 4,
        'Bucharest': 3,
        'Stuttgart': 4,
        'Mykonos': 2,
        'Helsinki': 5,
        'Split': 3,
        'London': 5,
        'Madrid': 2
    }
    
    cities_perm = ['Brussels', 'Bucharest', 'Stuttgart', 'Mykonos', 'Helsinki', 'Split', 'London']
    
    flight_list = [
        "Helsinki and London", 
        "Split and Madrid", 
        "Helsinki and Madrid", 
        "London and Madrid", 
        "Brussels and London", 
        "Bucharest and London", 
        "Brussels and Bucharest", 
        "Bucharest and Madrid", 
        "Split and Helsinki", 
        "Mykonos and Madrid", 
        "Stuttgart and London", 
        "Helsinki and Brussels", 
        "Brussels and Madrid", 
        "Split and London", 
        "Stuttgart and Split", 
        "London and Mykonos"
    ]
    
    graph = set()
    for flight in flight_list:
        a, b = flight.split(" and ")
        edge = frozenset([a, b])
        graph.add(edge)
        
    found_perm = None
    for perm in itertools.permutations(cities_perm):
        seq = list(perm)
        valid = True
        for i in range(len(seq)-1):
            a, b = seq[i], seq[i+1]
            if frozenset([a, b]) not in graph:
                valid = False
                break
        if not valid:
            continue
            
        if frozenset([seq[-1], 'Madrid']) not in graph:
            continue
            
        start = 1
        idx = seq.index('Stuttgart')
        for j in range(idx):
            start += days_dict[seq[j]] - 1
        if start > 4:
            continue
            
        found_perm = seq
        break
        
    if found_perm is None:
        print(json.dumps({"itinerary": []}))
        return
        
    itinerary = []
    current_start = 1
    for city in found_perm:
        end = current_start + days_dict[city] - 1
        itinerary.append({
            "day_range": f"Day {current_start}-{end}",
            "place": city
        })
        current_start = end
        
    end_madrid = current_start + days_dict['Madrid'] - 1
    itinerary.append({
        "day_range": f"Day {current_start}-{end_madrid}",
        "place": "Madrid"
    })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()