import itertools
import json

def main():
    cities_dict = {
        'Manchester': 3,
        'Istanbul': 7,
        'Venice': 7,
        'Krakow': 6,
        'Lyon': 2
    }
    
    flight_set = {
        ('Manchester', 'Venice'),
        ('Manchester', 'Istanbul'),
        ('Venice', 'Istanbul'),
        ('Istanbul', 'Krakow'),
        ('Venice', 'Lyon'),
        ('Lyon', 'Istanbul'),
        ('Manchester', 'Krakow')
    }
    
    remaining = ['Istanbul', 'Venice', 'Krakow', 'Lyon']
    found = False
    result_itinerary = None
    
    for perm in itertools.permutations(remaining):
        c2, c3, c4, c5 = perm
        d1 = cities_dict[c2]
        d2 = cities_dict[c3]
        d3 = cities_dict[c4]
        d4 = cities_dict[c5]
        
        if d4 != 22 - (d1 + d2 + d3):
            continue
        
        if not ((('Manchester', c2) in flight_set) or ((c2, 'Manchester') in flight_set)):
            continue
        if not (((c2, c3) in flight_set) or ((c3, c2) in flight_set)):
            continue
        if not (((c3, c4) in flight_set) or ((c4, c3) in flight_set)):
            continue
        if not (((c4, c5) in flight_set) or ((c5, c4) in flight_set)):
            continue
        
        venice_block = None
        if c2 == 'Venice':
            venice_block = 1
        elif c3 == 'Venice':
            venice_block = 2
        elif c4 == 'Venice':
            venice_block = 3
        elif c5 == 'Venice':
            venice_block = 4
        else:
            continue
        
        if venice_block == 4:
            continue
        elif venice_block == 3:
            if d1 + d2 > 8:
                continue
        
        e1 = 3
        e2 = d1 + 2
        e3 = d1 + d2 + 1
        e4 = d1 + d2 + d3
        
        itinerary = [
            {"day_range": "Day 1-3", "place": "Manchester"},
            {"day_range": f"Day 3-{e2}", "place": c2},
            {"day_range": f"Day {e2}-{e3}", "place": c3},
            {"day_range": f"Day {e3}-{e4}", "place": c4},
            {"day_range": f"Day {e4}-21", "place": c5}
        ]
        found = True
        result_itinerary = itinerary
        break
    
    if not found:
        result_itinerary = []
    
    print(json.dumps({'itinerary': result_itinerary}))

if __name__ == '__main__':
    main()