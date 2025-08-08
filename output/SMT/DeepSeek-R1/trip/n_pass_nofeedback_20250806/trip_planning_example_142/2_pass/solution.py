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
    
    # Constraint: Must end in Tallinn on day 7
    solver.add(s[6] == 2)  # s[6] corresponds to day 7
    
    # Add travel constraints for days 1 to 6
    for i in range(6):
        # Define the condition for a direct flight
        direct_flight = Or(
            And(s[i] == 0, s[i+1] == 1),
            And(s[i] == 1, s[i+1] == 0),
            And(s[i] == 1, s[i+1] == 2),
            And(s[i] == 2, s[i+1] == 1)
        )
        # If traveling, must be a direct flight; else, stay in the same city
        solver.add(If(t[i], direct_flight, s[i] == s[i+1]))
    
    # Count days for each city
    count_madrid = 0
    count_dublin = 0
    count_tallinn = 0
    
    # For each day, count the start city and if traveling, the arrival city
    for i in range(7):
        # Count the start city for day i+1
        count_madrid += If(s[i] == 0, 1, 0)
        count_dublin += If(s[i] == 1, 1, 0)
        count_tallinn += If(s[i] == 2, 1, 0)
        
        # If this day has a flight (and it's not the last day), count the arrival city
        if i < 6:
            count_madrid += If(And(t[i], s[i+1] == 0), 1, 0)
            count_dublin += If(And(t[i], s[i+1] == 1), 1, 0)
            count_tallinn += If(And(t[i], s[i+1] == 2), 1, 0)
    
    # Add constraints for the required days in each city
    solver.add(count_madrid == 4)
    solver.add(count_dublin == 3)
    solver.add(count_tallinn == 2)
    
    # Exactly two travel days
    total_travels = Sum([If(t_i, 1, 0) for t_i in t])
    solver.add(total_travels == 2)
    
    # Check for a solution
    if solver.check() == sat:
        m = solver.model()
        itinerary_list = []
        # Get the values for s and t
        s_vals = [m.evaluate(s_i).as_long() for s_i in s]
        t_vals = [m.evaluate(t_i) for t_i in t]
        
        # Build the itinerary
        for day in range(1, 8):  # days 1 to 7
            idx = day - 1  # index in s_vals and t_vals
            # Add the start city for the day
            start_city = city_names[s_vals[idx]]
            itinerary_list.append({'day': day, 'city': start_city})
            # If there's a flight on this day (and it's not the last day), add the arrival city
            if day < 7 and t_vals[idx]:
                arrival_city = city_names[s_vals[idx+1]]
                itinerary_list.append({'day': day, 'city': arrival_city})
        
        # Output as JSON
        output = {'itinerary': itinerary_list}
        print(output)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()