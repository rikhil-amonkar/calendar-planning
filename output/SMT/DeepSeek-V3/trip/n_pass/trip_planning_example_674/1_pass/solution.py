from z3 import *
import json

def solve_itinerary():
    cities = ['Helsinki', 'Warsaw', 'Madrid', 'Split', 'Reykjavik', 'Budapest']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    direct_flights = [
        ('Helsinki', 'Reykjavik'),
        ('Budapest', 'Warsaw'),
        ('Madrid', 'Split'),
        ('Helsinki', 'Split'),
        ('Helsinki', 'Madrid'),
        ('Helsinki', 'Budapest'),
        ('Reykjavik', 'Warsaw'),
        ('Helsinki', 'Warsaw'),
        ('Madrid', 'Budapest'),
        ('Budapest', 'Reykjavik'),
        ('Madrid', 'Warsaw'),
        ('Warsaw', 'Split'),
        ('Reykjavik', 'Madrid')
    ]
    # Create a set of tuples for direct flights (both directions)
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((city_to_idx[a], city_to_idx[b]))
        flight_pairs.add((city_to_idx[b], city_to_idx[a]))
    
    days_total = 14
    s = Solver()
    
    # day_city[i] is the city visited on day i+1 (1-based days)
    day_city = [Int(f'day_{i+1}') for i in range(days_total)]
    for dc in day_city:
        s.add(dc >= 0, dc < len(cities))
    
    # Fixed constraints:
    # Helsinki on days 1 and 2
    s.add(day_city[0] == city_to_idx['Helsinki'])
    s.add(day_city[1] == city_to_idx['Helsinki'])
    
    # Warsaw on days 9, 10, 11 (indices 8, 9, 10)
    s.add(day_city[8] == city_to_idx['Warsaw'])
    s.add(day_city[9] == city_to_idx['Warsaw'])
    s.add(day_city[10] == city_to_idx['Warsaw'])
    
    # Reykjavik on day 8 (index 7)
    s.add(day_city[7] == city_to_idx['Reykjavik'])
    
    # Flight transitions: consecutive days must be same city or connected by a flight
    for i in range(days_total - 1):
        current = day_city[i]
        next_ = day_city[i+1]
        s.add(Or(current == next_, (current, next_) in flight_pairs))
    
    # Total days per city (including flight days)
    # For each city, the total days is the sum of:
    # 1. Days assigned to the city.
    # 2. Days where the next day is a different city (flight day, counted for current city).
    # So for city c, total is Sum over i: (day_city[i] == c) + Sum over i < 13: (day_city[i] == c and day_city[i+1] != c)
    city_days_required = {
        'Helsinki': 2,
        'Warsaw': 3,
        'Madrid': 4,
        'Split': 4,
        'Reykjavik': 2,
        'Budapest': 4
    }
    
    for city, required in city_days_required.items():
        c = city_to_idx[city]
        # Total days is the number of days assigned to c plus the number of transitions out of c.
        total = Sum([If(day_city[i] == c, 1, 0) for i in range(days_total)]) + \
                Sum([If(And(day_city[i] == c, i < days_total - 1, day_city[i+1] != c), 1, 0) for i in range(days_total - 1)])
        s.add(total == required)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(1, days_total + 1):
            city_idx = m.evaluate(day_city[day-1]).as_long()
            itinerary.append({'day': day, 'place': cities[city_idx]})
        
        return json.dumps({'itinerary': itinerary}, indent=2)
    else:
        return json.dumps({'error': 'No solution found'}, indent=2)

print(solve_itinerary())