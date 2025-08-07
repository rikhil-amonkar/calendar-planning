from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Helsinki': 2,
        'Warsaw': 3,
        'Madrid': 4,
        'Split': 4,
        'Reykjavik': 2,
        'Budapest': 4
    }
    
    # Direct flights (bidirectional unless specified)
    direct_flights = [
        ('Helsinki', 'Reykjavik'),
        ('Budapest', 'Warsaw'),
        ('Madrid', 'Split'),
        ('Helsinki', 'Split'),  # Corrected to 'Helsinki'
        ('Helsinki', 'Madrid'),  # Corrected to 'Madrid'
        ('Helsinki', 'Budapest'),
        ('Reykjavik', 'Warsaw'),
        ('Helsinki', 'Warsaw'),
        ('Madrid', 'Budapest'),
        ('Budapest', 'Reykjavik'),
        ('Madrid', 'Warsaw'),  # Corrected to 'Madrid'
        ('Warsaw', 'Split'),
        ('Reykjavik', 'Madrid')  # One-way
    ]
    
    # Correct city name typos
    corrected_flights = []
    for flight in direct_flights:
        city1, city2 = flight
        if city1 == 'Helsinki' or city1 == 'Helsinki':
            city1 = 'Helsinki'
        if city2 == 'Helsinki' or city2 == 'Helsinki':
            city2 = 'Helsinki'
        if city1 == 'Madrid' or city1 == 'Madrid':
            city1 = 'Madrid'
        if city2 == 'Madrid' or city2 == 'Madrid':
            city2 = 'Madrid'
        corrected_flights.append((city1, city2))
    
    # Create flight pairs (bidirectional except one-way)
    flight_pairs = set()
    for flight in corrected_flights:
        A, B = flight
        flight_pairs.add((A, B))
        if (A, B) != ('Reykjavik', 'Madrid'):
            flight_pairs.add((B, A))
    
    # Create Z3 variables
    days = 14
    city_names = sorted(cities.keys())  # Ensure consistent ordering
    city_to_int = {city: idx for idx, city in enumerate(city_names)}
    int_to_city = {idx: city for city, idx in city_to_int.items()}
    
    day_vars = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    s = Solver()
    
    # Day variables must be valid city indices
    for day_var in day_vars:
        s.add(day_var >= 0, day_var < len(city_names))
    
    # Constraint 1: Helsinki on days 1 and 2
    s.add(day_vars[0] == city_to_int['Helsinki'])
    s.add(day_vars[1] == city_to_int['Helsinki'])
    
    # Constraint 2: Reykjavik between days 8-9
    s.add(Or(
        day_vars[7] == city_to_int['Reykjavik'],  # day 8
        day_vars[8] == city_to_int['Reykjavik']   # day 9
    ))
    
    # Constraint 3: Warsaw between days 9-11
    s.add(Or(
        day_vars[8] == city_to_int['Warsaw'],   # day 9
        day_vars[9] == city_to_int['Warsaw'],   # day 10
        day_vars[10] == city_to_int['Warsaw']   # day 11
    ))
    
    # Flight transitions between consecutive days
    for i in range(days - 1):
        current = day_vars[i]
        next_day = day_vars[i + 1]
        same_city = (current == next_day)
        possible_transitions = []
        for city1, city2 in flight_pairs:
            c1 = city_to_int[city1]
            c2 = city_to_int[city2]
            possible_transitions.append(And(current == c1, next_day == c2))
        s.add(Or(same_city, Or(possible_transitions)))
    
    # Total days in each city must match requirements
    for city, req_days in cities.items():
        city_idx = city_to_int[city]
        total = Sum([If(d == city_idx, 1, 0) for d in day_vars])
        s.add(total == req_days)
    
    # Additional constraints to help the solver
    # Must leave Helsinki after day 2
    s.add(day_vars[2] != city_to_int['Helsinki'])
    # Must be in Reykjavik for exactly 2 days
    # Must be in Warsaw for exactly 3 days
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(days):
            day_num = i + 1
            city_idx = model.evaluate(day_vars[i]).as_long()
            city = int_to_city[city_idx]
            itinerary.append({'day': day_num, 'place': city})
        
        # Verify the solution meets all requirements
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry['place']] += 1
        
        valid = True
        for city, req in cities.items():
            if city_days[city] != req:
                valid = False
                break
        
        if valid:
            return {'itinerary': itinerary}
    
    return None

result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))
else:
    print("No valid itinerary found.")