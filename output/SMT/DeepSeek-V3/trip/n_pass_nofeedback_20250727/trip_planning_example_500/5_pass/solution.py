from z3 import *
import json

def solve_itinerary():
    # Cities with correct spellings
    cities = ['Hamburg', 'Munich', 'Manchester', 'Lyon', 'Split']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Complete direct flights adjacency list
    direct_flights = {
        'Split': ['Munich', 'Lyon', 'Hamburg'],
        'Munich': ['Split', 'Manchester', 'Lyon', 'Hamburg'],
        'Manchester': ['Munich', 'Hamburg', 'Split'],
        'Hamburg': ['Manchester', 'Munich', 'Split'],
        'Lyon': ['Split', 'Munich']
    }
    
    # Create Z3 variables for each day's city
    days = 20
    X = [Int(f'X_{i}') for i in range(days)]
    
    s = Solver()
    
    # Each day's city must be a valid city index
    for i in range(days):
        s.add(And(X[i] >= 0, X[i] < len(cities)))
    
    # Transition constraints with proper flight connections
    for i in range(days - 1):
        current_city = X[i]
        next_city = X[i+1]
        # Either stay in same city or take a direct flight
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_to_idx[a], next_city == city_to_idx[b]) 
              for a in direct_flights for b in direct_flights[a]]
        ))
    
    # Duration constraints with proper counting
    # Hamburg: 7 days total
    s.add(Sum([If(X[i] == city_to_idx['Hamburg'], 1, 0) for i in range(days)]) == 7)
    # Munich: 6 days total
    s.add(Sum([If(X[i] == city_to_idx['Munich'], 1, 0) for i in range(days)]) == 6)
    # Manchester: must be on days 19-20 (indices 18-19)
    s.add(And(X[18] == city_to_idx['Manchester'], X[19] == city_to_idx['Manchester']))
    # Lyon: must be on days 13-14 (indices 12-13)
    s.add(And(X[12] == city_to_idx['Lyon'], X[13] == city_to_idx['Lyon']))
    # Split: 7 days total
    s.add(Sum([If(X[i] == city_to_idx['Split'], 1, 0) for i in range(days)]) == 7)
    
    # Additional constraints to prevent impossible sequences
    # Cannot be in Lyon except on days 13-14
    for i in range(days):
        if i not in [12, 13]:
            s.add(X[i] != city_to_idx['Lyon'])
    # Cannot be in Manchester except on days 19-20
    for i in range(days):
        if i not in [18, 19]:
            s.add(X[i] != city_to_idx['Manchester'])
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(days):
            city_idx = m.evaluate(X[i]).as_long()
            itinerary.append({'day': i+1, 'city': cities[city_idx]})
        
        # Verify all constraints are satisfied
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['city']] += 1
        
        assert counts['Hamburg'] == 7
        assert counts['Munich'] == 6
        assert counts['Manchester'] == 2
        assert counts['Lyon'] == 2
        assert counts['Split'] == 7
        assert itinerary[18]['city'] == 'Manchester'
        assert itinerary[19]['city'] == 'Manchester'
        assert itinerary[12]['city'] == 'Lyon'
        assert itinerary[13]['city'] == 'Lyon'
        
        # Verify flight transitions
        for i in range(days - 1):
            current = itinerary[i]['city']
            next_c = itinerary[i+1]['city']
            if current != next_c:
                assert next_c in direct_flights[current], f"Invalid flight from {current} to {next_c}"
        
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    print(json.dumps(result, indent=2))
else:
    print("No solution found")