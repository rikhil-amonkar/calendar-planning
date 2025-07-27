from z3 import *
import json

def solve_itinerary():
    # Cities and their integer mappings
    cities = ['Split', 'Vilnius', 'Santorini', 'Madrid']
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flight connections (bidirectional)
    connections = [
        ('Vilnius', 'Split'),
        ('Split', 'Madrid'),
        ('Madrid', 'Santorini')
    ]
    
    # Create connection indices for constraint checking
    connection_indices = set()
    for a, b in connections:
        connection_indices.add((city_to_int[a], city_to_int[b]))
        connection_indices.add((city_to_int[b], city_to_int[a]))
    
    # Total days and day variables
    num_days = 14
    day_vars = [Int(f'day_{i}') for i in range(1, num_days + 1)]
    
    # Initialize solver
    s = Solver()
    
    # Each day must be assigned to a valid city
    for day_var in day_vars:
        s.add(Or([day_var == idx for idx in range(len(cities))]))
    
    # Conference days (13-14) must be in Santorini
    s.add(day_vars[12] == city_to_int['Santorini'])  # day 13
    s.add(day_vars[13] == city_to_int['Santorini'])  # day 14
    
    # Transition constraints between consecutive days
    for i in range(num_days - 1):
        current = day_vars[i]
        next_day = day_vars[i + 1]
        s.add(Or(
            current == next_day,  # Stay in same city
            And(current != next_day, (current, next_day) in connection_indices)  # Valid flight
        ))
    
    # Duration constraints for each city
    split_days = sum([If(day_var == city_to_int['Split'], 1, 0) for day_var in day_vars])
    vilnius_days = sum([If(day_var == city_to_int['Vilnius'], 1, 0) for day_var in day_vars])
    santorini_days = sum([If(day_var == city_to_int['Santorini'], 1, 0) for day_var in day_vars])
    madrid_days = sum([If(day_var == city_to_int['Madrid'], 1, 0) for day_var in day_vars])
    
    s.add(split_days == 5)
    s.add(vilnius_days == 4)
    s.add(santorini_days == 2)  # Already enforced for days 13-14
    s.add(madrid_days == 6)
    
    # Additional constraint: Must visit all required cities
    s.add(Or([day_var == city_to_int['Split'] for day_var in day_vars]))
    s.add(Or([day_var == city_to_int['Vilnius'] for day_var in day_vars]))
    s.add(Or([day_var == city_to_int['Madrid'] for day_var in day_vars]))
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        itinerary = []
        int_to_city = {idx: city for city, idx in city_to_int.items()}
        
        for day in range(1, num_days + 1):
            city_idx = m.evaluate(day_vars[day - 1]).as_long()
            itinerary.append({'day': day, 'place': int_to_city[city_idx]})
        
        # Verify the solution
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        assert counts['Split'] == 5
        assert counts['Vilnius'] == 4
        assert counts['Santorini'] == 2
        assert counts['Madrid'] == 6
        
        # Verify transitions
        for i in range(num_days - 1):
            current = itinerary[i]['place']
            next_city = itinerary[i + 1]['place']
            if current != next_city:
                assert (current, next_city) in connections or (next_city, current) in connections
        
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate and print the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))