from z3 import *
import json

# Initialize solver
solver = Solver()

# Define variables
F1 = Int('F1')
F2 = Int('F2')

# Add constraints
solver.add(F1 >= 1)
solver.add(F2 >= F1 + 1)
solver.add(F2 <= 16)

# Constraints for the durations
solver.add(F1 == 7)
solver.add((F2 - F1) + 1 == 7)  # Lyon's duration
solver.add(17 - F2 == 4)        # Porto's duration

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    F1_val = model[F1].as_long()
    F2_val = model[F2].as_long()
    
    # Generate the itinerary
    itinerary = []
    
    # Bucharest: days 1 to F1-1
    for day in range(1, F1_val):
        itinerary.append({"day": day, "city": "Bucharest"})
    
    # Lyon: days F1 to F2-1
    for day in range(F1_val, F2_val):
        itinerary.append({"day": day, "city": "Lyon"})
    
    # Porto: days F2 to 16
    for day in range(F2_val, 17):
        itinerary.append({"day": day, "city": "Porto"})
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")