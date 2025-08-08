from z3 import *

def main():
    # Define the city mapping
    city_names = {0: 'Madrid', 1: 'Dublin', 2: 'Tallinn'}
    
    # Create the solver
    solver = Solver()
    
    # Create variables for the start city for each day (1 to 7)
    s = [Int(f's_{i}') for i in range(1, 8)]
    # Create travel variables for days 1 to 6
    t = [Bool(f't_{i}') for i in range(1, 7)]
    
    # Each s[i] must be 0, 1, or 2
    for i in range(7):
        solver.add(s[i] >= 0, s[i] <= 2)
    
    # Add travel constraints for days 1 to 6
    for i in range(6):
        # If traveling on day i+1, then the flight must be direct
        direct_flight = Or(
            And(s[i] == 0, s[i+1] == 1),
            And(s[i] == 1, s[i+1] == 0),
            And(s[i] == 1, s[i+1] == 2),
            And(s[i] == 2, s[i+1] == 1)
        )
        solver.add(If(t[i], direct_flight, s[i] == s[i+1]))
    
    # Count days for each city
    count_madrid = 0
    count_dublin = 0
    count_tallinn = 0
    
    # For days 1 to 6: being in a city c on day i if: start in c OR (travel and next city is c)
    for i in range(6):  # for day1 to day6 (index 0 to 5 in s, and t index 0 to 5)
        # Madrid (0)
        count_madrid += If(Or(s[i] == 0, And(t[i], s[i+1] == 0)), 1, 0)
        # Dublin (1)
        count_dublin += If(Or(s[i] == 1, And(t[i], s[i+1] == 1)), 1, 0)
        # Tallinn (2)
        count_tallinn += If(Or(s[i] == 2, And(t[i], s[i+1] == 2)), 1, 0)
    
    # Day7: only the start city
    count_madrid += If(s[6] == 0, 1, 0)
    count_dublin += If(s[6] == 1, 1, 0)
    count_tallinn += If(s[6] == 2, 1, 0)
    
    # Add count constraints
    solver.add(count_madrid == 4)
    solver.add(count_dublin == 3)
    solver.add(count_tallinn == 2)
    
    # Workshop constraint: must be in Tallinn on day7 and in Tallinn on day6
    solver.add(s[6] == 2)  # start of day7 is Tallinn
    # Being in Tallinn on day6: either start day6 in Tallinn or travel to Tallinn on day6 (which would set s[6] to Tallinn for day7)
    solver.add(Or(s[5] == 2, t[5]))  # day6 is index 5 in s and t
    
    # Exactly two travel days
    total_travels = Sum([If(t_i, 1, 0) for t_i in t])
    solver.add(total_travels == 2)
    
    # Check and get the model
    if solver.check() == sat:
        m = solver.model()
        itinerary = []
        # Evaluate s and t from the model
        s_vals = [m.evaluate(s_i) for s_i in s]
        t_vals = [m.evaluate(t_i) for t_i in t]
        
        # Map the integer values to city names
        s_cities = [city_names[int(str(val))] for val in s_vals]
        t_bool = [is_true(val) for val in t_vals]
        
        # Build the itinerary
        for day in range(1, 8):  # days 1 to 7
            # Day index in s: day-1
            idx = day - 1
            # Add the start city for the day
            itinerary.append({'day': day, 'city': s_cities[idx]})
            # If this day has travel (only for days 1 to 6) and travel occurred, add the arrival city
            if day <= 6 and t_bool[day-1]:
                # The arrival city is the start of the next day
                next_city = s_cities[idx+1]
                itinerary.append({'day': day, 'city': next_city})
        
        # Output as JSON
        output = {'itinerary': itinerary}
        print(output)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()