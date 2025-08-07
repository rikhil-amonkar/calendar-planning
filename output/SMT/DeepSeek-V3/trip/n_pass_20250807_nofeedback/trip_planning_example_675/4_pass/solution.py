from z3 import *
import json

def solve_itinerary():
    # Cities and their indices
    cities = ['Dubrovnik', 'Split', 'Milan', 'Porto', 'Krakow', 'Munich']
    city_map = {city: idx for idx, city in enumerate(cities)}
    idx_map = {idx: city for idx, city in enumerate(cities)}

    # Direct flights (bidirectional)
    direct_flights = [
        ('Munich', 'Porto'),
        ('Split', 'Milan'),
        ('Milan', 'Porto'),
        ('Munich', 'Krakow'),
        ('Munich', 'Milan'),
        ('Dubrovnik', 'Munich'),
        ('Krakow', 'Split'),
        ('Krakow', 'Milan'),
        ('Munich', 'Split')
    ]
    
    # Create adjacency list
    adjacency = {city: set() for city in cities}
    for a, b in direct_flights:
        adjacency[a].add(b)
        adjacency[b].add(a)

    # Z3 solver
    s = Solver()

    # Variables: day[i] represents the city on day i+1 (1-16)
    days = [Int(f'day_{i}') for i in range(16)]
    for day in days:
        s.add(day >= 0, day < len(cities))

    # Transition constraints
    for i in range(15):
        current = days[i]
        next_day = days[i+1]
        # Either stay in same city or move to adjacent city
        s.add(Or(
            current == next_day,
            *[And(current == city_map[a], next_day == city_map[b]) 
              for a in cities for b in adjacency[a]]
        ))

    # Duration constraints (including flight days)
    duration = {
        'Dubrovnik': 4,
        'Split': 3,
        'Milan': 3,
        'Porto': 4,
        'Krakow': 2,
        'Munich': 5
    }
    for city, req in duration.items():
        count = Sum([If(days[i] == city_map[city], 1, 0) for i in range(16)])
        s.add(count == req)

    # Event constraints
    # Munich show days 4-8 (0-based 3-7)
    for i in range(3, 8):
        s.add(days[i] == city_map['Munich'])

    # Krakow friends days 8-9 (0-based 7-8)
    s.add(days[7] == city_map['Krakow'])
    s.add(days[8] == city_map['Krakow'])

    # Milan wedding days 11-13 (0-based 10-12)
    for i in range(10, 13):
        s.add(days[i] == city_map['Milan'])

    # Solve and return itinerary
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(16):
            city_idx = model.evaluate(days[i]).as_long()
            itinerary.append({'day': i+1, 'place': idx_map[city_idx]})
        return json.dumps({'itinerary': itinerary}, indent=2)
    else:
        return json.dumps({'error': 'No valid itinerary found'}, indent=2)

print(solve_itinerary())