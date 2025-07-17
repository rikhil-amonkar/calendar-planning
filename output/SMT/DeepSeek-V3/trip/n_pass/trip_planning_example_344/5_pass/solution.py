from z3 import *

def solve_itinerary():
    # Cities with their IDs
    cities = ['Valencia', 'Athens', 'Naples', 'Zurich']
    city_ids = {city: idx for idx, city in enumerate(cities)}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Initialize solver
    s = Solver()
    
    # Decision variables: city for each day (1-20)
    day_city = [Int(f'day_{i}') for i in range(1, 21)]
    
    # Each day must be assigned to a valid city
    for day in day_city:
        s.add(And(day >= 0, day <= 3))
    
    # Fixed periods:
    # Days 1-6 in Athens
    for i in range(6):
        s.add(day_city[i] == city_ids['Athens'])
    
    # Days 16-20 in Naples
    for i in range(15, 20):
        s.add(day_city[i] == city_ids['Naples'])
    
    # Define direct flight connections (bidirectional)
    direct_flights = [
        (0, 2),  # Valencia-Naples
        (0, 1),  # Valencia-Athens
        (1, 2),  # Athens-Naples
        (3, 2),  # Zurich-Naples
        (1, 3),  # Athens-Zurich
        (3, 0)   # Zurich-Valencia
    ]
    
    # Ensure valid transitions between consecutive days
    for i in range(19):  # Days 1-19 transitioning to days 2-20
        current = day_city[i]
        next_day = day_city[i+1]
        
        # Either stay in same city or take a direct flight
        s.add(Or(
            current == next_day,
            *[And(current == c1, next_day == c2) for c1, c2 in direct_flights]
        ))
    
    # Count days in each city
    counts = [0]*4
    for day in day_city:
        for i in range(4):
            counts[i] += If(day == i, 1, 0)
    
    # Add constraints for total days in each city
    s.add(counts[city_ids['Valencia']] == 6)
    s.add(counts[city_ids['Athens']] == 6)
    s.add(counts[city_ids['Naples']] == 5)
    s.add(counts[city_ids['Zurich']] == 6)
    
    # Find a solution
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(20):
            city_id = m.evaluate(day_city[i]).as_long()
            itinerary.append({'day': i+1, 'place': id_to_city[city_id]})
        
        return {'itinerary': itinerary}
    else:
        print("No solution found")
        return None

result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))