import itertools
import json

def main():
    cities = ['Amsterdam', 'Vienna', 'Santorini', 'Lyon']
    durations = {'Amsterdam': 3, 'Vienna': 7, 'Santorini': 4, 'Lyon': 3}
    
    graph = {
        'Vienna': ['Lyon', 'Santorini', 'Amsterdam'],
        'Amsterdam': ['Vienna', 'Santorini', 'Lyon'],
        'Santorini': ['Vienna', 'Amsterdam'],
        'Lyon': ['Vienna', 'Amsterdam']
    }
    
    event_lyon = {7, 8, 9}
    event_amsterdam = {9, 10, 11}
    
    all_perms = list(itertools.permutations(cities))
    valid_orders = []
    
    for perm in all_perms:
        valid = True
        for i in range(len(perm) - 1):
            city1, city2 = perm[i], perm[i+1]
            if city2 not in graph[city1]:
                valid = False
                break
            if (city1 == 'Santorini' and city2 == 'Lyon') or (city1 == 'Lyon' and city2 == 'Santorini'):
                valid = False
                break
        if valid:
            valid_orders.append(perm)
    
    itinerary = None
    for perm in valid_orders:
        d1 = durations[perm[0]]
        d2 = durations[perm[1]]
        d3 = durations[perm[2]]
        d4 = durations[perm[3]]
        
        ranges = {
            perm[0]: (1, d1),
            perm[1]: (d1, d1 + d2 - 1),
            perm[2]: (d1 + d2 - 1, d1 + d2 + d3 - 2),
            perm[3]: (d1 + d2 + d3 - 2, 14)
        }
        
        if 'Lyon' in ranges:
            lyon_start, lyon_end = ranges['Lyon']
            lyon_days = set(range(lyon_start, lyon_end + 1))
            if not lyon_days.intersection(event_lyon):
                continue
        
        if 'Amsterdam' in ranges:
            amsterdam_start, amsterdam_end = ranges['Amsterdam']
            amsterdam_days = set(range(amsterdam_start, amsterdam_end + 1))
            if not amsterdam_days.intersection(event_amsterdam):
                continue
        
        itinerary = []
        for city in perm:
            start, end = ranges[city]
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range_str, "place": city})
        break
    
    if itinerary is None:
        itinerary = []
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()