from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['London', 'Santorini', 'Istanbul']
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Days are 1..10
    days = 10
    day_numbers = range(1, days + 1)
    
    # Create Z3 variables for each day's city
    assignments = [Int(f'day_{i}') for i in day_numbers]
    
    # Create solver
    solver = Solver()
    
    # Each day's assignment must be 0, 1, or 2 (representing the cities)
    for day in assignments:
        solver.add(day >= 0, day <= 2)
    
    # Direct flight connections: Istanbul <-> London, London <-> Santorini
    # So transitions between non-London cities are not allowed directly.
    for i in range(len(day_numbers) - 1):
        current_day = assignments[i]
        next_day = assignments[i + 1]
        # Constraint: if current and next day cities are different, they must have a direct flight
        solver.add(Implies(current_day != next_day, 
                          Or(
                              And(current_day == city_to_int['London'], next_day == city_to_int['Istanbul']),
                              And(current_day == city_to_int['Istanbul'], next_day == city_to_int['London']),
                              And(current_day == city_to_int['London'], next_day == city_to_int['Santorini']),
                              And(current_day == city_to_int['Santorini'], next_day == city_to_int['London'])
                          )))
    
    # Total days constraints
    # London: 3 days
    solver.add(Sum([If(assignments[i] == city_to_int['London'], 1, 0) for i in range(days)]) == 3)
    # Santorini: 6 days, including day 5 and 10 (1-based)
    solver.add(Sum([If(assignments[i] == city_to_int['Santorini'], 1, 0) for i in range(days)]) == 6)
    solver.add(assignments[4] == city_to_int['Santorini'])  # Day 5 (0-based index 4)
    solver.add(assignments[9] == city_to_int['Santorini'])  # Day 10 (0-based index 9)
    # Istanbul: 3 days
    solver.add(Sum([If(assignments[i] == city_to_int['Istanbul'], 1, 0) for i in range(days)]) == 3)
    
    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(days):
            day_num = i + 1
            city_idx = model.evaluate(assignments[i]).as_long()
            city = int_to_city[city_idx]
            itinerary.append({'day': day_num, 'place': city})
        
        # Convert to the required JSON format
        result = {'itinerary': itinerary}
        return json.dumps(result, indent=2)
    else:
        return json.dumps({'error': 'No valid itinerary found'}, indent=2)

# Execute and print the result
print(solve_itinerary())