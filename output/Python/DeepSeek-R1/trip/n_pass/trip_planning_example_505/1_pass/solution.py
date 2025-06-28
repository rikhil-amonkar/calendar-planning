import itertools
import json

def main():
    cities = ['Stuttgart', 'Split', 'Krakow', 'Prague', 'Florence']
    graph = {
        'Stuttgart': ['Split', 'Krakow'],
        'Split': ['Stuttgart', 'Krakow', 'Prague'],
        'Krakow': ['Stuttgart', 'Split', 'Prague'],
        'Prague': ['Split', 'Krakow', 'Florence'],
        'Florence': ['Prague']
    }
    
    for perm in itertools.permutations(cities):
        valid_path = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in graph[perm[i]]:
                valid_path = False
                break
        if not valid_path:
            continue
            
        durations = [4 if city == 'Prague' else 2 for city in perm]
        
        t1 = durations[0]
        t2 = t1 + durations[1] - 1
        t3 = t2 + durations[2] - 1
        t4 = t3 + durations[3] - 1
        d5 = 9 - t4
        if d5 != durations[4]:
            continue
            
        stuttgart_idx = perm.index('Stuttgart')
        split_idx = perm.index('Split')
        
        if stuttgart_idx == 0:
            start_st, end_st = 1, t1
        elif stuttgart_idx == 1:
            start_st, end_st = t1, t2
        elif stuttgart_idx == 2:
            start_st, end_st = t2, t3
        elif stuttgart_idx == 3:
            start_st, end_st = t3, t4
        else:
            start_st, end_st = t4, 8
            
        if not ((start_st <= 2 and end_st >= 2) or (start_st <= 3 and end_st >= 3)):
            continue
            
        if split_idx == 0:
            start_sp, end_sp = 1, t1
        elif split_idx == 1:
            start_sp, end_sp = t1, t2
        elif split_idx == 2:
            start_sp, end_sp = t2, t3
        elif split_idx == 3:
            start_sp, end_sp = t3, t4
        else:
            start_sp, end_sp = t4, 8
            
        if not ((start_sp <= 3 and end_sp >= 3) or (start_sp <= 4 and end_sp >= 4)):
            continue
            
        itinerary = [
            {"day_range": f"Day 1-{t1}", "place": perm[0]},
            {"day_range": f"Day {t1}-{t2}", "place": perm[1]},
            {"day_range": f"Day {t2}-{t3}", "place": perm[2]},
            {"day_range": f"Day {t3}-{t4}", "place": perm[3]},
            {"day_range": f"Day {t4}-8", "place": perm[4]}
        ]
        
        print(json.dumps({"itinerary": itinerary}))
        return
    
    print(json.dumps({"error": "No valid itinerary found"}))
    
if __name__ == "__main__":
    main()