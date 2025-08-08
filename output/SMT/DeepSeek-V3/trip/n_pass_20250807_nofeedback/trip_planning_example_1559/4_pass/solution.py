from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Valencia': 2,
        'Oslo': 3,
        'Lyon': 4,
        'Prague': 3,
        'Paris': 4,
        'Nice': 4,
        'Seville': 5,
        'Tallinn': 2,
        'Mykonos': 5,
        'Lisbon': 2
    }
    city_list = list(cities.keys())
    city_map = {city: i for i, city in enumerate(city_list)}
    num_days = 25

    # Direct flights (bidirectional)
    direct_flights = [
        ('Lisbon', 'Paris'),
        ('Lyon', 'Nice'),
        ('Tallinn', 'Oslo'),
        ('Prague', 'Lyon'),
        ('Paris', 'Oslo'),
        ('Lisbon', 'Seville'),
        ('Prague', 'Lisbon'),
        ('Oslo', 'Nice'),
        ('Valencia', 'Paris'),
        ('Valencia', 'Lisbon'),
        ('Paris', 'Nice'),
        ('Nice', 'Mykonos'),
        ('Paris', 'Lyon'),
        ('Valencia', 'Lyon'),
        ('Prague', 'Oslo'),
        ('Prague', 'Paris'),
        ('Seville', 'Paris'),
        ('Oslo', 'Lyon'),
        ('Prague', 'Valencia'),
        ('Lisbon', 'Nice'),
        ('Lisbon', 'Oslo'),
        ('Valencia', 'Seville'),
        ('Lisbon', 'Lyon'),
        ('Paris', 'Tallinn'),
        ('Prague', 'Tallinn')
    ]

    # Make flight connections bidirectional
    flight_graph = {city: set() for city in city_list}
    for a, b in direct_flights:
        flight_graph[a].add(b)
        flight_graph[b].add(a)

    # Z3 variables
    day = [Int(f'day_{i}') for i in range(num_days)]
    s = Solver()

    # Each day must be one of the cities
    for d in day:
        s.add(And(d >= 0, d < len(city_list)))

    # Duration constraints
    for city, days in cities.items():
        s.add(sum([If(day[i] == city_map[city], 1, 0) for i in range(num_days)]) == days)

    # Event constraints
    # Valencia between day 3-4 (0-based 2-3)
    s.add(Or(day[2] == city_map['Valencia'], day[3] == city_map['Valencia']))
    
    # Oslo between day 13-15 (0-based 12-14)
    s.add(Or([day[i] == city_map['Oslo'] for i in range(12, 15)]))
    
    # Seville days 5-9 (0-based 4-8)
    for i in range(4, 9):
        s.add(day[i] == city_map['Seville'])
    
    # Mykonos days 21-25 (0-based 20-24)
    for i in range(20, 25):
        s.add(day[i] == city_map['Mykonos'])

    # Flight constraints
    for i in range(num_days - 1):
        current = day[i]
        next_day = day[i + 1]
        # Either stay in same city or fly to connected city
        s.add(Or(
            current == next_day,
            *[And(current == city_map[a], next_day == city_map[b]) 
              for a in flight_graph for b in flight_graph[a]]
        ))

    # Additional constraints to help solver
    # Ensure we don't have too many consecutive same cities
    for i in range(num_days - 3):
        s.add(Not(And(day[i] == day[i+1], day[i] == day[i+2], day[i] == day[i+3])))

    # Try to find solution with a timeout
    s.set("timeout", 30000)  # 30 seconds timeout
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(num_days):
            city_idx = m.evaluate(day[i]).as_long()
            itinerary.append({'day': i + 1, 'city': city_list[city_idx]})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found within constraints'}

# Generate and print the itinerary
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))