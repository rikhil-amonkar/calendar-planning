import json
from z3 import *

def solve_itinerary():
    # Cities with their indices
    cities = ['Berlin', 'Split', 'Bucharest', 'Riga', 'Lisbon', 'Tallinn', 'Lyon']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (bidirectional)
    direct_flights = [
        ('Lisbon', 'Bucharest'), ('Berlin', 'Lisbon'),
        ('Bucharest', 'Riga'), ('Berlin', 'Riga'),
        ('Split', 'Lyon'), ('Lisbon', 'Riga'),
        ('Riga', 'Tallinn'), ('Berlin', 'Split'),
        ('Lyon', 'Lisbon'), ('Berlin', 'Tallinn'),
        ('Lyon', 'Bucharest')
    ]
    
    # Make flights bidirectional and convert to indices
    flight_pairs = []
    for fr, to in direct_flights:
        flight_pairs.append((city_map[fr], city_map[to]))
        flight_pairs.append((city_map[to], city_map[fr]))
    
    # Duration requirements
    required_days = {
        'Berlin': 5,
        'Split': 3,
        'Bucharest': 3,
        'Riga': 5,
        'Lisbon': 3,
        'Tallinn': 4,
        'Lyon': 5
    }
    
    # Fixed events
    fixed_events = [
        (1, 5, 'Berlin'),
        (7, 11, 'Lyon'),
        (13, 15, 'Bucharest')
    ]
    
    # Create solver with timeout
    s = Solver()
    s.set("timeout", 30000)  # 30 second timeout
    
    # Day variables (1-22)
    days = [Int(f'day_{i+1}') for i in range(22)]
    
    # Each day must be a valid city index
    for day in days:
        s.add(day >= 0, day < 7)
    
    # Apply fixed events
    for start, end, city in fixed_events:
        city_idx = city_map[city]
        for day in range(start-1, end):  # 0-based indexing
            s.add(days[day] == city_idx)
    
    # Count days per city
    for city, req in required_days.items():
        city_idx = city_map[city]
        s.add(Sum([If(d == city_idx, 1, 0) for d in days]) == req)
    
    # Flight transitions
    for i in range(21):
        current = days[i]
        next_day = days[i+1]
        # Either stay in same city or take a direct flight
        s.add(Or(current == next_day, 
               Or([And(current == fr, next_day == to) for fr, to in flight_pairs])))
    
    # Additional constraints to help guide the solver
    # 1. Prefer longer stays in cities
    for i in range(20):
        s.add(Implies(days[i] != days[i+1], days[i+1] != days[i+2]))
    
    # 2. Avoid single-day visits unless necessary
    for i in range(1, 21):
        s.add(Implies(days[i-1] != days[i], days[i] != days[i+1])))
    
    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(22):
            day_num = i + 1
            city_idx = model.evaluate(days[i]).as_long()
            city = cities[city_idx]
            itinerary.append({'day': day_num, 'place': city})
        
        # Verify the solution meets all requirements
        city_counts = {city: 0 for city in cities}
        for entry in itinerary:
            city_counts[entry['place']] += 1
        
        valid = True
        for city, req in required_days.items():
            if city_counts[city] != req:
                valid = False
                break
        
        if valid:
            return {'itinerary': itinerary}
    
    return None

# Solve and print the itinerary
itinerary = solve_itinerary()
if itinerary:
    print(json.dumps(itinerary, indent=2))
else:
    print("No valid itinerary found.")