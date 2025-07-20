import itertools
import json

def main():
    cities = ['Reykjavik', 'Istanbul', 'Edinburgh', 'Oslo', 'Stuttgart', 'Bucharest']
    days_required = {
        'Reykjavik': 5,
        'Istanbul': 4,
        'Edinburgh': 5,
        'Oslo': 2,
        'Stuttgart': 3,
        'Bucharest': 5
    }
    
    graph = {
        'Bucharest': ['Oslo', 'Istanbul'],
        'Oslo': ['Bucharest', 'Istanbul', 'Reykjavik', 'Edinburgh'],
        'Istanbul': ['Oslo', 'Bucharest', 'Edinburgh', 'Stuttgart'],
        'Reykjavik': ['Stuttgart', 'Oslo'],
        'Stuttgart': ['Istanbul', 'Edinburgh'],
        'Edinburgh': ['Stuttgart', 'Istanbul', 'Oslo']
    }
    
    for perm in itertools.permutations(cities):
        valid_flight = True
        for i in range(5):
            if perm[i+1] not in graph[perm[i]]:
                valid_flight = False
                break
        if not valid_flight:
            continue
        
        cum_sum = 0
        start_days = []
        for i, city in enumerate(perm):
            start = 1 + cum_sum - i
            start_days.append(start)
            cum_sum += days_required[city]
        end_days = [start_days[i] + days_required[city] - 1 for i, city in enumerate(perm)]
        
        istanbul_idx = perm.index('Istanbul')
        oslo_idx = perm.index('Oslo')
        
        istanbul_start = start_days[istanbul_idx]
        istanbul_end = end_days[istanbul_idx]
        if not (istanbul_end >= 5 and istanbul_start <= 8):
            continue
            
        oslo_start = start_days[oslo_idx]
        oslo_end = end_days[oslo_idx]
        if not (oslo_end >= 8 and oslo_start <= 9):
            continue
            
        itinerary_list = []
        for i in range(6):
            start = start_days[i]
            end = end_days[i]
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary_list.append({"day_range": day_range_str, "place": perm[i]})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
        return
    
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()