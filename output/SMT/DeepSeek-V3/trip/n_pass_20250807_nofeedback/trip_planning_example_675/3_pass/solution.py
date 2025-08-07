from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Dubrovnik', 'Split', 'Milan', 'Porto', 'Krakow', 'Munich']
    city_map = {city: idx for idx, city in enumerate(cities)}
    idx_map = {idx: city for idx, city in enumerate(cities)}
    
    # Direct flights: list of tuples (from, to)
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
    # Ensure bidirectional
    all_flights = set()
    for a, b in direct_flights:
        all_flights.add((a, b))
        all_flights.add((b, a))
    
    # Create an adjacency list
    adjacency = {city: set() for city in cities}
    for a, b in all_flights:
        adjacency[a].add(b)
    
    # Z3 solver
    s = Solver()
    
    # Variables: day[i] is the city on day i+1 (days 1..16)
    days = [Int(f'day_{i}') for i in range(16)]
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Transition constraints: consecutive days must be same city or connected by flight
    for i in range(15):
        current_city = days[i]
        next_city = days[i+1]
        # Either same city or connected by flight
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_map[a], next_city == city_map[b]) for a in cities for b in adjacency[a]]
        ))
    
    # Duration constraints
    duration = {
        'Dubrovnik': 4,
        'Split': 3,
        'Milan': 3,
        'Porto': 4,
        'Krakow': 2,
        'Munich': 5
    }
    for city, required in duration.items():
        city_idx = city_map[city]
        count = Sum([If(days[i] == city_idx, 1, 0) for i in range(16)])
        s.add(count == required)
    
    # Event constraints
    # Munich show between day 4-8 (days 3..7 in 0-based)
    for i in range(3, 8):
        s.add(days[i] == city_map['Munich'])
    
    # Krakow friends between day 8-9 (days 7..8 in 0-based)
    s.add(days[7] == city_map['Krakow'])
    s.add(days[8] == city_map['Krakow'])
    
    # Milan wedding between day 11-13 (days 10..12 in 0-based)
    s.add(days[10] == city_map['Milan'])
    s.add(days[11] == city_map['Milan'])
    s.add(days[12] == city_map['Milan'])
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(16):
            city_idx = model.evaluate(days[i]).as_long()
            city = idx_map[city_idx]
            itinerary.append({'day': i+1, 'place': city})
        
        # Verify the itinerary meets all constraints
        # (This step is for validation; omitted here for brevity)
        
        # Return as JSON
        result = {'itinerary': itinerary}
        return json.dumps(result, indent=2)
    else:
        return json.dumps({"error": "No solution found"}, indent=2)

print(solve_itinerary())