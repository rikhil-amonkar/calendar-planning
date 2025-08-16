from z3 import *
import json

# Define variables for start and end days of each city
start_L, end_L = Ints('start_L end_L')
start_S, end_S = Ints('start_S end_S')
start_O, end_O = Ints('start_O end_O')
start_P, end_P = Ints('start_P end_P')

# Initialize the solver
s = Solver()

# Add constraints for the duration of each city
s.add(end_L == start_L + 7 - 1)  # London: 7 days
s.add(end_S == start_S + 5 - 1)  # Split: 5 days
s.add(end_O == start_O + 2 - 1)  # Oslo: 2 days
s.add(end_P == start_P + 5 - 1)  # Porto: 5 days

# Add constraints for consecutive city transitions
s.add(end_L == start_S)  # London to Split
s.add(end_S == start_O)  # Split to Oslo
s.add(end_O == start_P)  # Oslo to Porto

# Add constraint for the start of Split
s.add(start_S == 7)

# Add constraint for the end of the trip
s.add(end_P == 16)

# Check if the constraints are satisfiable
if s.check() == sat:
    m = s.model()
    
    # Extract the values from the model
    start_L_val = m.evaluate(start_L).as_long()
    end_L_val = m.evaluate(end_L).as_long()
    start_S_val = m.evaluate(start_S).as_long()
    end_S_val = m.evaluate(end_S).as_long()
    start_O_val = m.evaluate(start_O).as_long()
    end_O_val = m.evaluate(end_O).as_long()
    start_P_val = m.evaluate(start_P).as_long()
    end_P_val = m.evaluate(end_P).as_long()
    
    # Generate the itinerary
    itinerary = []
    for day in range(1, 17):
        city = None
        # Check in reverse order to assign flight days to the destination city
        if day >= start_P_val and day <= end_P_val:
            city = "Porto"
        elif day >= start_O_val and day <= end_O_val:
            city = "Oslo"
        elif day >= start_S_val and day <= end_S_val:
            city = "Split"
        elif day >= start_L_val and day <= end_L_val:
            city = "London"
        itinerary.append({"day": day, "city": city})
    
    # Output the result in JSON format
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")