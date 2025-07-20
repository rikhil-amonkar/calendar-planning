import itertools
import json

def main():
    total_days = 16
    cities = ['Barcelona', 'Oslo', 'Stuttgart', 'Venice', 'Split', 'Brussels', 'Copenhagen']
    days_req = {
        'Barcelona': 3,
        'Oslo': 2,
        'Stuttgart': 3,
        'Venice': 4,
        'Split': 4,
        'Brussels': 3,
        'Copenhagen': 3
    }
    
    flight_connections = [
        ('Venice', 'Stuttgart'),
        ('Oslo', 'Brussels'),
        ('Split', 'Copenhagen'),
        ('Barcelona', 'Copenhagen'),
        ('Barcelona', 'Venice'),
        ('Brussels', 'Venice'),
        ('Barcelona', 'Stuttgart'),
        ('Copenhagen', 'Brussels'),
        ('Oslo', 'Split'),
        ('Oslo', 'Venice'),
        ('Barcelona', 'Split'),
        ('Oslo', 'Copenhagen'),
        ('Barcelona', 'Oslo'),
        ('Copenhagen', 'Stuttgart'),
        ('Split', 'Stuttgart'),
        ('Copenhagen', 'Venice'),
        ('Barcelona', 'Brussels')
    ]
    
    graph = {}
    for c in cities:
        graph[c] = set()
    for a, b in flight_connections:
        graph[a].add(b)
        graph[b].add(a)
    
    start_city = 'Barcelona'
    remaining = [c for c in cities if c != start_city]
    
    found_schedule = None
    for perm in itertools.permutations(remaining):
        path = [start_city] + list(perm)
        valid_path = True
        for i in range(1, len(path)):
            if path[i] not in graph[path[i-1]]:
                valid_path = False
                break
        if not valid_path:
            continue
            
        current_start = 1
        schedule = []
        for city in path:
            dur = days_req[city]
            end_day = current_start + dur - 1
            schedule.append((city, current_start, end_day))
            current_start = end_day
            
        if schedule[-1][2] > total_days:
            continue
            
        oslo_ok = False
        brussels_ok = False
        for (city, start, end) in schedule:
            if city == 'Oslo':
                if start <= 4 and end >= 3:
                    oslo_ok = True
            if city == 'Brussels':
                if start <= 11 and end >= 9:
                    brussels_ok = True
                    
        if oslo_ok and brussels_ok:
            found_schedule = schedule
            break
            
    itinerary_list = []
    if found_schedule is not None:
        for (city, start, end) in found_schedule:
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary_list.append({"day_range": day_range_str, "place": city})
    else:
        itinerary_list = []
        
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == '__main__':
    main()