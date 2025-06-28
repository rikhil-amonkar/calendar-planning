import itertools
import json

def main():
    durations = {
        'Stuttgart': 2,
        'Split': 2,
        'Krakow': 2,
        'Prague': 4,
        'Florence': 2
    }
    graph = {
        'Stuttgart': ['Split', 'Krakow'],
        'Split': ['Stuttgart', 'Krakow', 'Prague'],
        'Krakow': ['Stuttgart', 'Split', 'Prague'],
        'Prague': ['Split', 'Krakow', 'Florence'],
        'Florence': ['Prague']
    }
    total_days = 8
    required = {'Stuttgart', 'Split'}
    all_cities = list(durations.keys())
    
    subsets = []
    for r in range(len(required), len(all_cities) + 1):
        for combo in itertools.combinations(all_cities, r):
            combo_set = set(combo)
            if combo_set >= required and 'Prague' in combo_set:
                total_duration = sum(durations[city] for city in combo)
                if total_duration == total_days:
                    subsets.append(combo)
    
    for subset in subsets:
        remaining = [city for city in subset if city != 'Stuttgart' and city != 'Prague']
        for mid_perm in itertools.permutations(remaining):
            perm = ('Stuttgart',) + mid_perm + ('Prague',)
            valid_path = True
            for i in range(len(perm) - 1):
                if perm[i + 1] not in graph[perm[i]]:
                    valid_path = False
                    break
            if not valid_path:
                continue
                
            start_days = [1]
            for i in range(1, len(perm)):
                start_days.append(start_days[i - 1] + durations[perm[i - 1]])
            end_days = [start_days[i] + durations[perm[i]] - 1 for i in range(len(perm))]
            
            stuttgart_ok = False
            idx = perm.index('Stuttgart')
            start = start_days[idx]
            end = end_days[idx]
            if (start <= 2 <= end) or (start <= 3 <= end):
                stuttgart_ok = True
            
            split_ok = False
            if 'Split' in perm:
                idx = perm.index('Split')
                start = start_days[idx]
                end = end_days[idx]
                if (start <= 3 <= end) or (start <= 4 <= end):
                    split_ok = True
            
            if stuttgart_ok and split_ok:
                itinerary = []
                for i in range(len(perm)):
                    start = start_days[i]
                    end = end_days[i]
                    if start == end:
                        day_range = f"Day {start}"
                    else:
                        day_range = f"Day {start}-{end}"
                    itinerary.append({
                        "day_range": day_range,
                        "place": perm[i]
                    })
                print(json.dumps({"itinerary": itinerary}))
                return
    
    print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == "__main__":
    main()