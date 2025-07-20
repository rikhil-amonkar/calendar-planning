import itertools
import json

def main():
    graph = {
        'Porto': {'Amsterdam', 'Munich'},
        'Prague': {'Reykjavik', 'Amsterdam', 'Munich'},
        'Reykjavik': {'Prague', 'Amsterdam', 'Munich'},
        'Munich': {'Porto', 'Amsterdam', 'Reykjavik', 'Prague'},
        'Amsterdam': {'Porto', 'Munich', 'Reykjavik', 'Prague', 'Santorini'},
        'Santorini': {'Amsterdam'}
    }
    
    found = False
    itinerary_result = None
    
    for end1 in range(1, 15):
        for end2 in range(end1, 15):
            for end3 in range(end2, 15):
                L1 = end1
                L2 = end2 - end1 + 1
                L3 = end3 - end2 + 1
                L4 = 14 - end3 + 1
                lengths = [L1, L2, L3, L4]
                if sorted(lengths) == [4, 4, 4, 5]:
                    cities = ['Porto', 'Prague', 'Reykjavik', 'Munich']
                    for perm in itertools.permutations(cities):
                        assignment = list(perm)
                        valid = True
                        if assignment[1] not in graph[assignment[0]]:
                            valid = False
                        if valid and assignment[2] not in graph[assignment[1]]:
                            valid = False
                        if valid and assignment[3] not in graph[assignment[2]]:
                            valid = False
                        if valid and 'Amsterdam' not in graph[assignment[3]]:
                            valid = False
                        if not valid:
                            continue
                        
                        idx_r = assignment.index('Reykjavik')
                        if idx_r == 0:
                            start_r, end_r = 1, end1
                        elif idx_r == 1:
                            start_r, end_r = end1, end2
                        elif idx_r == 2:
                            start_r, end_r = end2, end3
                        else:
                            start_r, end_r = end3, 14
                        if not (start_r <= 7 and end_r >= 4):
                            continue
                            
                        idx_m = assignment.index('Munich')
                        if idx_m == 0:
                            start_m, end_m = 1, end1
                        elif idx_m == 1:
                            start_m, end_m = end1, end2
                        elif idx_m == 2:
                            start_m, end_m = end2, end3
                        else:
                            start_m, end_m = end3, 14
                        if not (start_m <= 10 and end_m >= 7):
                            continue
                            
                        itinerary_list = [
                            {"day_range": f"Day 1-{end1}", "place": assignment[0]},
                            {"day_range": f"Day {end1}-{end2}", "place": assignment[1]},
                            {"day_range": f"Day {end2}-{end3}", "place": assignment[2]},
                            {"day_range": f"Day {end3}-14", "place": assignment[3]},
                            {"day_range": "Day 14-15", "place": "Amsterdam"},
                            {"day_range": "Day 15-16", "place": "Santorini"}
                        ]
                        itinerary_result = {"itinerary": itinerary_list}
                        found = True
                        break
                    if found:
                        break
                if found:
                    break
            if found:
                break
        if found:
            break
            
    if not found:
        itinerary_result = {"itinerary": []}
        
    print(json.dumps(itinerary_result))

if __name__ == "__main__":
    main()