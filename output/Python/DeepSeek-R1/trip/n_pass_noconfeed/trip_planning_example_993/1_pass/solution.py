import itertools
import json

def main():
    cities = ['Riga', 'Frankfurt', 'Amsterdam', 'Vilnius', 'London', 'Stockholm', 'Bucharest']
    durations = {
        'Riga': 2,
        'Frankfurt': 3,
        'Amsterdam': 2,
        'Vilnius': 5,
        'London': 2,
        'Stockholm': 3,
        'Bucharest': 4
    }
    constraints = {
        'Amsterdam': (2, 3),
        'Vilnius': (7, 11),
        'Stockholm': (13, 15)
    }
    flight_list = [
        ('London', 'Amsterdam'),
        ('Vilnius', 'Frankfurt'),
        ('Riga', 'Vilnius'),
        ('Riga', 'Stockholm'),
        ('London', 'Bucharest'),
        ('Amsterdam', 'Stockholm'),
        ('Amsterdam', 'Frankfurt'),
        ('Frankfurt', 'Stockholm'),
        ('Bucharest', 'Riga'),
        ('Amsterdam', 'Riga'),
        ('Amsterdam', 'Bucharest'),
        ('Riga', 'Frankfurt'),
        ('Bucharest', 'Frankfurt'),
        ('London', 'Frankfurt'),
        ('London', 'Stockholm'),
        ('Amsterdam', 'Vilnius')
    ]
    flight_set = set()
    for a, b in flight_list:
        flight_set.add((a, b))
        flight_set.add((b, a))
    
    valid_permutation_found = False
    result_itinerary = None
    
    for perm in itertools.permutations(cities):
        valid_flight = True
        for i in range(len(perm)-1):
            if (perm[i], perm[i+1]) not in flight_set:
                valid_flight = False
                break
        if not valid_flight:
            continue
            
        total_duration_so_far = 0
        satisfies_constraints = True
        starts = {}
        for idx, city in enumerate(perm):
            start_day = 1 + total_duration_so_far - idx
            starts[city] = start_day
            dur = durations[city]
            if city in constraints:
                low, high = constraints[city]
                end_day = start_day + dur - 1
                if not (start_day <= high and end_day >= low):
                    satisfies_constraints = False
                    break
            total_duration_so_far += dur
            
        if satisfies_constraints:
            valid_permutation_found = True
            itinerary_list = []
            for city in perm:
                start = starts[city]
                dur_val = durations[city]
                end = start + dur_val - 1
                day_range_str = f"Day {start}-{end}" if dur_val > 1 else f"Day {start}"
                itinerary_list.append({"day_range": day_range_str, "place": city})
            result_itinerary = {"itinerary": itinerary_list}
            break
            
    if not valid_permutation_found:
        result_itinerary = {"itinerary": []}
        
    print(json.dumps(result_itinerary))

if __name__ == "__main__":
    main()