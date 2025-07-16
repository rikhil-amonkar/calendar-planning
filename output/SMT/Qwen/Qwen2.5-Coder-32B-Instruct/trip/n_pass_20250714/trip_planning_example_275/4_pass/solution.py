from z3 import *

# Define the variables for the start day of each city
start_split = Int('start_split')
start_vilnius = Int('start_vilnius')
start_madrid = Int('start_madrid')
start_santorini = Int('start_santorini')

# Define the duration for each city
duration_split = 5
duration_vilnius = 4
duration_madrid = 6
duration_santorini = 2

# Create the solver
solver = Solver()

# Add constraints for the total number of days
solver.add(start_split >= 1)
solver.add(start_vilnius == start_split + duration_split - 1)
solver.add(start_madrid == start_vilnius + duration_vilnius - 1)
solver.add(start_santorini == start_madrid + duration_madrid - 1)
solver.add(start_santorini + duration_santorini == 14)

# Ensure that the conference days are in Santorini
solver.add(start_santorini <= 13)
solver.add(start_santorini + duration_santorini >= 14)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    start_split_val = model[start_split].as_long()
    start_vilnius_val = model[start_vilnius].as_long()
    start_madrid_val = model[start_madrid].as_long()
    start_santorini_val = model[start_santorini].as_long()
    
    # Generate the itinerary
    itinerary = []
    
    # Split
    itinerary.append({"day_range": f"Day {start_split_val}-{start_split_val + duration_split - 1}", "place": "Split"})
    itinerary.append({"day_range": f"Day {start_split_val + duration_split - 1}", "place": "Split"})
    itinerary.append({"day_range": f"Day {start_split_val + duration_split - 1}", "place": "Vilnius"})
    
    # Vilnius
    itinerary.append({"day_range": f"Day {start_vilnius_val}-{start_vilnius_val + duration_vilnius - 1}", "place": "Vilnius"})
    itinerary.append({"day_range": f"Day {start_vilnius_val + duration_vilnius - 1}", "place": "Vilnius"})
    itinerary.append({"day_range": f"Day {start_vilnius_val + duration_vilnius - 1}", "place": "Madrid"})
    
    # Madrid
    itinerary.append({"day_range": f"Day {start_madrid_val}-{start_madrid_val + duration_madrid - 1}", "place": "Madrid"})
    itinerary.append({"day_range": f"Day {start_madrid_val + duration_madrid - 1}", "place": "Madrid"})
    itinerary.append({"day_range": f"Day {start_madrid_val + duration_madrid - 1}", "place": "Santorini"})
    
    # Santorini
    itinerary.append({"day_range": f"Day {start_santorini_val}-{start_santorini_val + duration_santorini - 1}", "place": "Santorini"})
    
    # Print the itinerary in JSON format
    print({"itinerary": itinerary})
else:
    print("No solution found")