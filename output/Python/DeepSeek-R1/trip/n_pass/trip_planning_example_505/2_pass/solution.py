import itertools
import json

def main():
    cities = ['Stuttgart', 'Split', 'Krakow', 'Prague', 'Florence']
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
    for perm in itertools.permutations(cities):
        # Check valid travel path
        valid_path = True
        for i in range(len(perm)-1):
            if perm[i+1] not in graph[perm[i]]:
                valid_path = False
                break
        if not valid_path:
            continue
            
        # Calculate start days and check total
        start_days = [1]
        for i in range(1, len(perm)):
            start_days.append(start_days[i-1] + durations[perm[i-1]])
        end_days = [start_days[i] + durations[perm[i]] - 1 for i in range(len(perm))]
        
        # Check if entire trip fits in 8 days
        if end_days[-1] != total_days:
            continue
            
        # Check Stuttgart and Split day constraints
        stuttgart_index = perm.index('Stuttgart')
        stuttgart_days = (start_days[stuttgart_index], end_days[stuttgart_index])
        if not (stuttgart_days[0] <= 2 <= stuttgart_days[1] or 
                stuttgart_days[0] <= 3 <= stuttgart_days[1]):
            continue
            
        split_index = perm.index('Split')
        split_days = (start_days[split_index], end_days[split_index])
        if not (split_days[0] <= 3 <= split_days[1] or 
                split_days[0] <= 4 <= split_days[1]):
            continue
            
        # Build itinerary with non-overlapping ranges
        itinerary = []
        for i in range(len(perm)):
            start = start_days[i]
            end = end_days[i]
            # Format day range as "Day X-Y" for multi-day stays
            day_range = f"Day {start}-{end}" if end > start else f"Day {start}"
            itinerary.append({"day_range": day_range, "place": perm[i]})
        
        print(json.dumps({"itinerary": itinerary}))
        return
    
    print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == "__main__":
    main()