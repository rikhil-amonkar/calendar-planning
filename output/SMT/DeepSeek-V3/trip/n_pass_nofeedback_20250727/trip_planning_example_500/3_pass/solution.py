from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Hamburg', 'Munich', 'Manchester', 'Lyon', 'Split']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        'Split': ['Munich', 'Lyon', 'Hamburg'],
        'Munich': ['Split', 'Manchester', 'Lyon', 'Hamburg'],
        'Manchester': ['Munich', 'Hamburg', 'Split'],
        'Hamburg': ['Manchester', 'Munich', 'Split'],
        'Lyon': ['Split', 'Munich']
    }
    
    # Create Z3 variables: for each day, which city (as an integer index)
    days = 20
    X = [Int(f'X_{i}') for i in range(days)]
    
    s = Solver()
    
    # Each day's city must be 0-4 (indices of cities)
    for i in range(days):
        s.add(And(X[i] >= 0, X[i] < len(cities)))
    
    # Transition constraints: consecutive days must be either same city or connected by direct flight
    for i in range(days - 1):
        current_city = X[i]
        next_city = X[i+1]
        # Either stay in the same city or move to a connected city
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_to_idx[a], next_city == city_to_idx[b]) 
              for a in direct_flights for b in direct_flights[a]]
        ))
    
    # Duration constraints
    # Hamburg: 7 days
    s.add(Sum([If(X[i] == city_to_idx['Hamburg'], 1, 0) for i in range(days)]) == 7)
    # Munich: 6 days
    s.add(Sum([If(X[i] == city_to_idx['Munich'], 1, 0) for i in range(days)]) == 6)
    # Manchester: 2 days (days 19 and 20)
    s.add(And(X[18] == city_to_idx['Manchester'], X[19] == city_to_idx['Manchester']))
    # Lyon: 2 days, including days 13-14 (indices 12 and 13)
    s.add(And(X[12] == city_to_idx['Lyon'], X[13] == city_to_idx['Lyon']))
    # Split: 7 days
    s.add(Sum([If(X[i] == city_to_idx['Split'], 1, 0) for i in range(days)]) == 7)
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        city_names = ['Hamburg', 'Munich', 'Manchester', 'Lyon', 'Split']
        for i in range(days):
            city_idx = m.evaluate(X[i]).as_long()
            itinerary.append({'day': i+1, 'city': city_names[city_idx]})
        
        # Verify transitions are valid
        for i in range(days - 1):
            current_city = itinerary[i]['city']
            next_city = itinerary[i+1]['city']
            if current_city != next_city:
                assert next_city in direct_flights[current_city], f"Invalid flight from {current_city} to {next_city}"
        
        # Verify durations
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['city']] += 1
        assert counts['Hamburg'] == 7
        assert counts['Munich'] == 6
        assert counts['Manchester'] == 2
        assert counts['Lyon'] == 2
        assert counts['Split'] == 7
        assert itinerary[18]['city'] == 'Manchester' and itinerary[19]['city'] == 'Manchester'
        assert itinerary[12]['city'] == 'Lyon' and itinerary[13]['city'] == 'Lyon'
        
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    print(json.dumps(result, indent=2))
else:
    print("No solution found")