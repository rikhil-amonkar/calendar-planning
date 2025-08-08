from z3 import *
import json

def solve_itinerary():
    # Cities and their indices
    cities = ['Amsterdam', 'Vienna', 'Santorini', 'Lyon']
    city_idx = {city: i for i, city in enumerate(cities)}
    
    # Direct flight connections
    connections = {
        0: [1, 2, 3],  # Amsterdam
        1: [0, 2, 3],   # Vienna
        2: [0, 1],      # Santorini
        3: [0, 1]       # Lyon
    }
    
    s = Solver()
    
    # Day variables (1-14)
    days = [Int(f'd_{i}') for i in range(14)]
    for day in days:
        s.add(day >= 0, day <= 3)
    
    # Total days per city
    city_days = [sum([If(days[i] == idx, 1, 0) for i in range(14)]) for idx in range(4)]
    s.add(city_days[city_idx['Amsterdam']] == 3)
    s.add(city_days[city_idx['Vienna']] == 7)
    s.add(city_days[city_idx['Santorini']] == 4)
    s.add(city_days[city_idx['Lyon']] == 3)
    
    # Workshop in Amsterdam (days 9-11)
    s.add(Or([days[i] == city_idx['Amsterdam'] for i in range(8, 11)]))
    
    # Wedding in Lyon (days 7-9)
    s.add(Or([days[i] == city_idx['Lyon'] for i in range(6, 9)]))
    
    # Flight transitions
    for i in range(13):
        current = days[i]
        next_day = days[i+1]
        s.add(Or(
            current == next_day,
            And(current != next_day, 
                Or([next_day == conn for conn in connections[current.as_long()]]))
        ))
    
    if s.check() == sat:
        m = s.model()
        itinerary = [{'day': i+1, 'place': cities[m[days[i]].as_long()]} for i in range(14)]
        
        # Verify counts
        counts = {city: 0 for city in cities}
        for day in itinerary:
            counts[day['place']] += 1
        
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

print(json.dumps(solve_itinerary(), indent=2))