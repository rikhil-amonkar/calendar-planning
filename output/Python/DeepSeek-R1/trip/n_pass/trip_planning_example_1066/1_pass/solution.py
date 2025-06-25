import itertools
import json

def main():
    durations = {
        'Brussels': 4,
        'Bucharest': 3,
        'Stuttgart': 4,
        'Mykonos': 2,
        'Madrid': 2,
        'Helsinki': 5,
        'Split': 3,
        'London': 5
    }
    
    graph = {
        'Helsinki': ['London', 'Madrid', 'Split', 'Brussels'],
        'Split': ['Madrid', 'Helsinki', 'London', 'Stuttgart'],
        'Madrid': ['Split', 'Helsinki', 'London', 'Mykonos', 'Bucharest', 'Brussels'],
        'London': ['Helsinki', 'Madrid', 'Brussels', 'Bucharest', 'Split', 'Mykonos', 'Stuttgart'],
        'Brussels': ['London', 'Bucharest', 'Madrid', 'Helsinki'],
        'Bucharest': ['London', 'Brussels', 'Madrid'],
        'Mykonos': ['Madrid', 'London'],
        'Stuttgart': ['London', 'Split']
    }
    
    cities_to_permute = ['Brussels', 'Bucharest', 'Stuttgart', 'Mykonos', 'Helsinki', 'Split', 'London']
    fixed_last = 'Madrid'
    
    found = False
    valid_order = None
    
    for perm in itertools.permutations(cities_to_permute):
        order = list(perm) + [fixed_last]
        valid_flight = True
        for i in range(len(order)-1):
            if order[i+1] not in graph[order[i]]:
                valid_flight = False
                break
        if not valid_flight:
            continue
            
        try:
            k = order.index('Stuttgart')
        except ValueError:
            continue
            
        if k == 0:
            start_stuttgart = 1
        else:
            total_prev = sum(durations[city] for city in order[:k])
            start_stuttgart = 1 + total_prev - k
            
        if start_stuttgart <= 4:
            found = True
            valid_order = order
            break
            
    if not found:
        result = {"itinerary": []}
        print(json.dumps(result))
        return
        
    itinerary_list = []
    cumulative_duration = 0
    for idx, city in enumerate(valid_order):
        if idx == 0:
            start_day = 1
            end_day = start_day + durations[city] - 1
        else:
            start_day = 1 + cumulative_duration - idx
            end_day = start_day + durations[city] - 1
        
        if start_day == end_day:
            day_range_str = f"Day {start_day}"
        else:
            day_range_str = f"Day {start_day}-{end_day}"
            
        itinerary_list.append({
            "day_range": day_range_str,
            "place": city
        })
        
        cumulative_duration += durations[city]
        
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == '__main__':
    main()