from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Hamburg', 'Munich', 'Manchester', 'Lyon', 'Split']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    idx_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        'Split': ['Munich', 'Lyon', 'Hamburg'],
        'Munich': ['Split', 'Manchester', 'Hamburg', 'Lyon'],
        'Manchester': ['Munich', 'Hamburg', 'Split'],
        'Hamburg': ['Manchester', 'Munich', 'Split'],
        'Lyon': ['Split', 'Munich']
    }
    
    # Create Z3 variables: for each day, which city are we in?
    days = 20
    X = [Int(f'X_{i}') for i in range(days)]
    
    s = Solver()
    
    # Each day's assignment must be a valid city index (0 to 4)
    for x in X:
        s.add(And(x >= 0, x <= 4))
    
    # Fixed constraints:
    # Manchester on days 19 and 20 (indices 18 and 19)
    s.add(X[18] == city_to_idx['Manchester'])
    s.add(X[19] == city_to_idx['Manchester'])
    
    # Lyon on days 13 and 14 (indices 12 and 13)
    s.add(X[12] == city_to_idx['Lyon'])
    s.add(X[13] == city_to_idx['Lyon'])
    
    # Flight transitions: consecutive days must be connected by direct flights
    for i in range(days - 1):
        current_city = X[i]
        next_city = X[i+1]
        # The next city must be in the direct_flights list of the current city
        # We create a disjunction of possible transitions
        constraints = []
        for city in cities:
            for neighbor in direct_flights.get(city, []):
                constraints.append(And(current_city == city_to_idx[city], next_city == city_to_idx[neighbor]))
        s.add(Or(constraints))
    
    # Duration constraints:
    # Count days per city, including overlapping flight days
    counts = {city: 0 for city in cities}
    for city in cities:
        counts[city] = Sum([If(X[i] == city_to_idx[city], 1, 0) for i in range(days)])
    
    s.add(counts['Hamburg'] == 7)
    s.add(counts['Munich'] == 6)
    s.add(counts['Manchester'] == 2)
    s.add(counts['Lyon'] == 2)
    s.add(counts['Split'] == 7)
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(days):
            city_idx = m.evaluate(X[i]).as_long()
            itinerary.append({'day': i+1, 'city': idx_to_city[city_idx]})
        
        # Verify transitions
        valid = True
        for i in range(days - 1):
            current_city = itinerary[i]['city']
            next_city = itinerary[i+1]['city']
            if next_city not in direct_flights[current_city]:
                valid = False
                print(f"Invalid transition from {current_city} to {next_city} on day {i+1}")
                break
        if not valid:
            raise ValueError("Invalid transitions in itinerary")
        
        # Verify counts
        count_check = {city: 0 for city in cities}
        for entry in itinerary:
            count_check[entry['city']] += 1
        expected_counts = {
            'Hamburg': 7,
            'Munich': 6,
            'Manchester': 2,
            'Lyon': 2,
            'Split': 7
        }
        for city in cities:
            if count_check[city] != expected_counts[city]:
                print(f"Count mismatch for {city}: {count_check[city]} vs {expected_counts[city]}")
                valid = False
        if not valid:
            raise ValueError("Count mismatch in itinerary")
        
        return {'itinerary': itinerary}
    else:
        raise ValueError("No valid itinerary found")

# Generate and print the itinerary
try:
    itinerary = solve_itinerary()
    print(itinerary)
except ValueError as e:
    print(e)