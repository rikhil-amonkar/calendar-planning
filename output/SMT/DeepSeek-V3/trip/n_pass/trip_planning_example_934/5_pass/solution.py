from z3 import *
import json

def solve_itinerary():
    # Cities and their indices
    cities = ['Brussels', 'Rome', 'Dubrovnik', 'Geneva', 'Budapest', 'Riga', 'Valencia']
    city_indices = {city: idx for idx, city in enumerate(cities)}
    
    # Corrected direct flights with proper city names
    direct_flights = {
        'Brussels': ['Valencia', 'Geneva', 'Riga', 'Rome', 'Budapest'],
        'Rome': ['Valencia', 'Geneva', 'Riga', 'Budapest', 'Brussels', 'Dubrovnik'],
        'Dubrovnik': ['Geneva', 'Rome'],
        'Geneva': ['Brussels', 'Rome', 'Dubrovnik', 'Valencia', 'Budapest'],
        'Budapest': ['Geneva', 'Rome', 'Brussels'],
        'Riga': ['Rome', 'Brussels'],
        'Valencia': ['Brussels', 'Rome', 'Geneva']
    }
    
    # Create allowed transitions including staying in same city
    allowed_transitions = {}
    for city in cities:
        allowed = direct_flights[city] + [city]
        allowed_indices = [city_indices[c] for c in allowed]
        allowed_transitions[city_indices[city]] = allowed_indices
    
    solver = Solver()
    
    # Day variables (1-17)
    days = [Int(f'day_{i}') for i in range(1, 18)]
    for day in days:
        solver.add(day >= 0, day < len(cities))
    
    # Total days constraints
    required_days = {
        'Brussels': 5,
        'Rome': 2,
        'Dubrovnik': 3,
        'Geneva': 5,
        'Budapest': 2,
        'Riga': 4,
        'Valencia': 2
    }
    
    for city, idx in city_indices.items():
        solver.add(sum([If(day == idx, 1, 0) for day in days) == required_days[city])
    
    # Flight constraints between consecutive days
    for i in range(len(days)-1):
        current = days[i]
        next_day = days[i+1]
        solver.add(Or([And(current == from_idx, Or([next_day == to_idx for to_idx in allowed_transitions[from_idx]]))
                     for from_idx in range(len(cities))])
    
    # Specific constraints
    # Brussels workshop between days 7-11 (at least one day)
    solver.add(Or([days[i] == city_indices['Brussels'] for i in range(6, 11)]))
    
    # Budapest meeting on day 16 or 17
    solver.add(Or(days[15] == city_indices['Budapest'], days[16] == city_indices['Budapest']))
    
    # Riga friends between days 4-7 (at least one day)
    solver.add(Or([days[i] == city_indices['Riga'] for i in range(3, 7)]))
    
    # Additional constraints to help the solver
    # Ensure first day is one of the cities with most connections
    solver.add(Or(days[0] == city_indices['Brussels'], 
                 days[0] == city_indices['Rome'],
                 days[0] == city_indices['Geneva']))
    
    # Try to find solution with a timeout
    solver.set("timeout", 30000)  # 30 seconds timeout
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(1, 18):
            day_var = days[i-1]
            city_idx = model[day_var].as_long()
            itinerary.append({'day': i, 'city': cities[city_idx]})
        
        # Verify counts
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['city']] += 1
        
        # Verify transitions
        valid = True
        for i in range(len(itinerary)-1):
            current = itinerary[i]['city']
            next_city = itinerary[i+1]['city']
            if next_city not in direct_flights[current] and next_city != current:
                valid = False
                break
        
        if valid and all(counts[city] == required_days[city] for city in cities):
            return {'itinerary': itinerary}
    
    return {"error": "No valid itinerary found"}

# Generate and print itinerary
itinerary = solve_itinerary()
print(json.dumps(itinerary, indent=2))