from z3 import *

def solve_itinerary():
    # Create a solver instance
    s = Solver()

    # Days are 1-based index up to 12
    days = 12
    cities = {'Brussels': 1, 'Barcelona': 2, 'Split': 3}
    
    # Create variables for each day: 1 = Brussels, 2 = Barcelona, 3 = Split
    day_vars = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    # Add constraints for each day variable to be 1, 2, or 3
    for day in day_vars:
        s.add(Or(day == 1, day == 2, day == 3))
    
    # Constraint: Days 1 and 2 must be Brussels (1)
    s.add(day_vars[0] == 1)
    s.add(day_vars[1] == 1)
    
    # Constraints for flights: transitions are only possible between connected cities
    for i in range(days - 1):
        current = day_vars[i]
        next_day = day_vars[i + 1]
        # Possible transitions:
        # Brussels <-> Barcelona, Barcelona <-> Split
        s.add(Or(
            current == next_day,  # stay in the same city
            And(current == 1, next_day == 2),  # Brussels to Barcelona
            And(current == 2, next_day == 1),  # Barcelona to Brussels
            And(current == 2, next_day == 3),  # Barcelona to Split
            And(current == 3, next_day == 2)   # Split to Barcelona
        ))
    
    # Count the number of days in each city
    brussels_days = Sum([If(day == 1, 1, 0) for day in day_vars])
    barcelona_days = Sum([If(day == 2, 1, 0) for day in day_vars])
    split_days = Sum([If(day == 3, 1, 0) for day in day_vars])
    
    # Add constraints for the required days in each city
    s.add(brussels_days == 2)
    s.add(barcelona_days == 7)
    s.add(split_days == 5)
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        city_names = {1: 'Brussels', 2: 'Barcelona', 3: 'Split'}
        for i in range(days):
            day_num = i + 1
            city_var = day_vars[i]
            city_val = model[city_var].as_long()
            itinerary.append({'day': day_num, 'place': city_names[city_val]})
        
        # Prepare the output as a JSON-formatted dictionary
        output = {'itinerary': itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

# Execute the function and print the result
result = solve_itinerary()
print(result)