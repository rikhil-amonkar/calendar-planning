import itertools
import json

def main():
    graph = {
        "Dubrovnik": ["Stockholm", "Copenhagen"],
        "Lisbon": ["Copenhagen", "Lyon", "Stockholm", "Prague"],
        "Copenhagen": ["Dubrovnik", "Stockholm", "Split", "Prague", "Tallinn", "Lisbon"],
        "Prague": ["Stockholm", "Lyon", "Lisbon", "Split", "Copenhagen", "Tallinn"],
        "Tallinn": ["Stockholm", "Copenhagen", "Prague"],
        "Stockholm": ["Dubrovnik", "Copenhagen", "Prague", "Tallinn", "Split", "Lisbon"],
        "Split": ["Copenhagen", "Stockholm", "Lyon", "Prague"],
        "Lyon": ["Lisbon", "Prague", "Split"]
    }
    
    days_req = {
        "Tallinn": 2,
        "Dubrovnik": 5,
        "Copenhagen": 5,
        "Prague": 3,
        "Stockholm": 4,
        "Split": 3,
        "Lisbon": 2,
        "Lyon": 2
    }
    
    fixed_start = "Tallinn"
    fixed_end = "Lyon"
    all_cities = list(days_req.keys())
    middle_cities = [city for city in all_cities if city != fixed_start and city != fixed_end]
    
    found_itinerary = None
    
    for perm in itertools.permutations(middle_cities):
        order = [fixed_start] + list(perm) + [fixed_end]
        valid = True
        for i in range(len(order)-1):
            if order[i+1] not in graph[order[i]]:
                valid = False
                break
        if not valid:
            continue
        
        starts = []
        ends = []
        start0 = 1
        end0 = start0 + days_req[order[0]] - 1
        starts.append(start0)
        ends.append(end0)
        
        for i in range(1, len(order)):
            start_i = ends[i-1]
            end_i = start_i + days_req[order[i]] - 1
            starts.append(start_i)
            ends.append(end_i)
        
        if ends[-1] != 19:
            continue
        
        try:
            idx_lisbon = order.index("Lisbon")
        except ValueError:
            continue
        
        if not (starts[idx_lisbon] <= 4 <= ends[idx_lisbon] or starts[idx_lisbon] <= 5 <= ends[idx_lisbon]):
            continue
        
        try:
            idx_stockholm = order.index("Stockholm")
        except ValueError:
            continue
        
        if ends[idx_stockholm] < 13 or starts[idx_stockholm] > 16:
            continue
        
        found_itinerary = []
        for i in range(len(order)):
            day_range_str = "Day {}-{}".format(starts[i], ends[i])
            found_itinerary.append({"day_range": day_range_str, "place": order[i]})
        break
    
    if found_itinerary is None:
        result = {"itinerary": []}
    else:
        result = {"itinerary": found_itinerary}
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()