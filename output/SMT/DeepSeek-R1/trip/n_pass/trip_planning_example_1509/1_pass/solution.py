from z3 import *
import json

def main():
    cities = ['Paris', 'Warsaw', 'Krakow', 'Tallinn', 'Riga', 'Copenhagen', 'Helsinki', 'Oslo', 'Santorini', 'Lyon']
    durations = {
        'Paris': 5,
        'Warsaw': 2,
        'Krakow': 2,
        'Tallinn': 2,
        'Riga': 2,
        'Copenhagen': 5,
        'Helsinki': 5,
        'Oslo': 5,
        'Santorini': 2,
        'Lyon': 4
    }
    fixed_starts = {
        'Krakow': 17,
        'Riga': 23,
        'Santorini': 12
    }
    
    bidirectional_pairs = [
        ('Warsaw', 'Riga'),
        ('Warsaw', 'Tallinn'),
        ('Copenhagen', 'Helsinki'),
        ('Lyon', 'Paris'),
        ('Copenhagen', 'Warsaw'),
        ('Lyon', 'Oslo'),
        ('Paris', 'Oslo'),
        ('Paris', 'Riga'),
        ('Krakow', 'Helsinki'),
        ('Paris', 'Tallinn'),
        ('Oslo', 'Riga'),
        ('Krakow', 'Warsaw'),
        ('Paris', 'Helsinki'),
        ('Copenhagen', 'Santorini'),
        ('Helsinki', 'Warsaw'),
        ('Helsinki', 'Riga'),
        ('Copenhagen', 'Krakow'),
        ('Copenhagen', 'Riga'),
        ('Paris', 'Krakow'),
        ('Copenhagen', 'Oslo'),
        ('Oslo', 'Tallinn'),
        ('Oslo', 'Helsinki'),
        ('Copenhagen', 'Tallinn'),
        ('Oslo', 'Krakow')
    ]
    directed_edges = [
        ('Riga', 'Tallinn'),
        ('Santorini', 'Oslo')
    ]
    
    allowed_edges = set()
    for (a, b) in bidirectional_pairs:
        allowed_edges.add((a, b))
        allowed_edges.add((b, a))
    for (a, b) in directed_edges:
        allowed_edges.add((a, b))
    
    pos = {city: Int(f'pos_{city}') for city in cities}
    s = Solver()
    
    for city in cities:
        s.add(pos[city] >= 0)
        s.add(pos[city] < 10)
    s.add(Distinct([pos[city] for city in cities]))
    
    start = {}
    for city in cities:
        sum_before = 0
        for other in cities:
            if other == city:
                continue
            sum_before += If(pos[other] < pos[city], durations[other], 0)
        start[city] = 1 + sum_before - pos[city]
    
    for city, fixed_start in fixed_starts.items():
        s.add(start[city] == fixed_start)
    
    s.add(start['Paris'] <= 8)
    s.add(And(start['Helsinki'] >= 15, start['Helsinki'] <= 21))
    
    for c0 in cities:
        for c1 in cities:
            if c0 == c1:
                continue
            if (c0, c1) not in allowed_edges:
                s.add(pos[c1] != pos[c0] + 1)
    
    if s.check() == sat:
        m = s.model()
        pos_val = {}
        for city in cities:
            pos_val[city] = m.eval(pos[city]).as_long()
        
        start_val = {}
        for city in cities:
            start_val[city] = m.eval(start[city]).as_long()
        
        order = sorted(cities, key=lambda city: pos_val[city])
        
        itinerary = []
        for idx, city in enumerate(order):
            s0 = start_val[city]
            e0 = s0 + durations[city] - 1
            itinerary.append({"day_range": f"Day {s0}-{e0}", "place": city})
            if idx < len(order) - 1:
                itinerary.append({"day_range": f"Day {e0}", "place": city})
                next_city = order[idx + 1]
                itinerary.append({"day_range": f"Day {e0}", "place": next_city})
        
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()