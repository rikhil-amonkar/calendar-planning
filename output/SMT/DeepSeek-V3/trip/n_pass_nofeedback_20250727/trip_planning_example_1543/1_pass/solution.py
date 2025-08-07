import json
from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Prague': 3,
        'Warsaw': 4,
        'Dublin': 3,
        'Athens': 3,
        'Vilnius': 4,
        'Porto': 5,
        'London': 3,
        'Seville': 2,
        'Lisbon': 5,
        'Dubrovnik': 3
    }
    
    city_list = sorted(cities.keys())
    city_to_int = {city: idx for idx, city in enumerate(city_list)}
    int_to_city = {idx: city for idx, city in enumerate(city_list)}
    
    # Direct flights: list of tuples
    direct_flights = [
        ('Warsaw', 'Vilnius'),
        ('Prague', 'Athens'),
        ('London', 'Lisbon'),
        ('Lisbon', 'Porto'),
        ('Prague', 'Lisbon'),
        ('London', 'Dublin'),
        ('Athens', 'Vilnius'),
        ('Athens', 'Dublin'),
        ('Prague', 'London'),
        ('London', 'Warsaw'),
        ('Dublin', 'Seville'),
        ('Seville', 'Porto'),
        ('Lisbon', 'Athens'),
        ('Dublin', 'Porto'),
        ('Athens', 'Warsaw'),
        ('Lisbon', 'Warsaw'),
        ('Porto', 'Warsaw'),
        ('Prague', 'Warsaw'),
        ('Prague', 'Dublin'),
        ('Athens', 'Dubrovnik'),
        ('Lisbon', 'Dublin'),
        ('Dubrovnik', 'Dublin'),
        ('Lisbon', 'Seville'),
        ('London', 'Athens')
    ]
    
    # Create a set of allowed transitions (both directions)
    allowed_transitions = set()
    for a, b in direct_flights:
        allowed_transitions.add((city_to_int[a], city_to_int[b]))
        allowed_transitions.add((city_to_int[b], city_to_int[a]))
    
    # Create Z3 variables for each day
    s = Solver()
    day_vars = [Int(f'day_{i}') for i in range(1, 27)]
    
    # Each day variable must be a valid city index
    for day in day_vars:
        s.add(And(day >= 0, day < len(city_list)))
    
    # Fixed constraints
    # Prague between day 1 and 3 (inclusive)
    for day in range(1, 4):  # days 1, 2, 3
        s.add(day_vars[day-1] == city_to_int['Prague'])
    
    # Workshop in Prague between day 1 and 3 (already covered)
    
    # Warsaw: 4 days, meet friends between day 20-23
    # So at least some of the 4 days must be between 20-23
    # We'll require that all 4 days are within 20-23 (simplifying)
    # Alternatively, ensure that the 4 days include at least the 4 days from 20-23 (but Warsaw's total is 4)
    # So the 4 days must be exactly 20-23.
    for day in range(20, 24):  # days 20,21,22,23
        s.add(day_vars[day-1] == city_to_int['Warsaw'])
    
    # London: 3 days, wedding between day 3-5
    # So the 3 days must include day 3,4,5
    for day in range(3, 6):  # days 3,4,5
        s.add(day_vars[day-1] == city_to_int['London'])
    
    # Porto: 5 days, conference between day 16-20
    # So the 5 days must include days 16-20 (5 days)
    for day in range(16, 21):  # days 16-20
        s.add(day_vars[day-1] == city_to_int['Porto'])
    
    # Lisbon: 5 days, relatives between day 5-9
    for day in range(5, 10):  # days 5-9
        s.add(day_vars[day-1] == city_to_int['Lisbon'])
    
    # Other cities' durations must be met
    for city, days in cities.items():
        city_idx = city_to_int[city]
        s.add(Sum([If(day_vars[i] == city_idx, 1, 0) for i in range(26)]) == days)
    
    # Flight transitions: consecutive days must be either same city or connected by direct flight
    for i in range(25):
        current_day = day_vars[i]
        next_day = day_vars[i+1]
        s.add(Or(
            current_day == next_day,
            And(current_day != next_day, (current_day, next_day) in allowed_transitions)
        ))
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, 27):
            city_idx = model.evaluate(day_vars[day-1]).as_long()
            itinerary.append({"day": day, "place": int_to_city[city_idx]})
        
        # Verify the solution meets all constraints
        # (This is a sanity check; Z3 should have ensured it)
        # Output the itinerary as JSON
        output = {"itinerary": itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))