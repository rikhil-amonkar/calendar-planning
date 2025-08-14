from z3 import *

# Define the solver
solver = Solver()

# Define the variables for the start day of each city
start_day_prague = Int('start_day_prague')
start_day_berlin = Int('start_day_berlin')
start_day_tallinn = Int('start_day_tallinn')
start_day_stockholm = Int('start_day_stockholm')

# Define the durations for each city
duration_prague = 2
duration_berlin = 3
duration_tallinn = 5
duration_stockholm = 5

# Define the constraints
# Stay in Berlin from day 6 to day 8 (inclusive)
solver.add(start_day_berlin <= 5)  # Ensure Berlin starts before day 6
solver.add(start_day_berlin + duration_berlin >= 9)  # Ensure Berlin ends after day 8

# Visit relatives in Tallinn between day 8 and day 12 (inclusive)
solver.add(start_day_tallinn <= 7)  # Ensure Tallinn starts before day 8
solver.add(start_day_tallinn + duration_tallinn >= 8)  # Ensure Tallinn includes day 8

# Flight constraints
# Flight from Prague to Tallinn or Stockholm
solver.add(Or(
    And(start_day_prague + duration_prague == start_day_tallinn),
    And(start_day_prague + duration_prague == start_day_stockholm)
))

# Flight from Berlin to Tallinn
solver.add(start_day_berlin + duration_berlin == start_day_tallinn)

# Flight from Tallinn to Stockholm
solver.add(start_day_tallinn + duration_tallinn == start_day_stockholm)

# Ensure the total duration is 12 days
solver.add(start_day_stockholm + duration_stockholm == 12)

# Ensure all start days are non-negative
solver.add(start_day_prague >= 0)
solver.add(start_day_berlin >= 0)
solver.add(start_day_tallinn >= 0)
solver.add(start_day_stockholm >= 0)

# Ensure the itinerary covers exactly 12 days
solver.add(start_day_prague == 0)  # Start in Prague on day 1

# Ensure the days are consecutive and valid
solver.add(start_day_berlin >= start_day_prague + duration_prague - 1)
solver.add(start_day_tallinn >= start_day_berlin + duration_berlin - 1)
solver.add(start_day_stockholm >= start_day_tallinn + duration_tallinn - 1)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []

    # Extract the start days from the model
    start_day_prague_val = model[start_day_prague].as_long()
    start_day_berlin_val = model[start_day_berlin].as_long()
    start_day_tallinn_val = model[start_day_tallinn].as_long()
    start_day_stockholm_val = model[start_day_stockholm].as_long()

    # Create the itinerary
    itinerary.append({"day_range": f"Day {start_day_prague_val+1}-{start_day_prague_val + duration_prague}", "place": "Prague"})
    itinerary.append({"day_range": f"Day {start_day_prague_val + duration_prague}", "place": "Prague"})
    
    if start_day_prague_val + duration_prague == start_day_tallinn_val:
        itinerary.append({"day_range": f"Day {start_day_prague_val + duration_prague}", "place": "Tallinn"})
    elif start_day_prague_val + duration_prague == start_day_stockholm_val:
        itinerary.append({"day_range": f"Day {start_day_prague_val + duration_prague}", "place": "Stockholm"})

    itinerary.append({"day_range": f"Day {start_day_berlin_val+1}-{start_day_berlin_val + duration_berlin}", "place": "Berlin"})
    itinerary.append({"day_range": f"Day {start_day_berlin_val + duration_berlin}", "place": "Berlin"})
    itinerary.append({"day_range": f"Day {start_day_berlin_val + duration_berlin}", "place": "Tallinn"})

    itinerary.append({"day_range": f"Day {start_day_tallinn_val+1}-{start_day_tallinn_val + duration_tallinn}", "place": "Tallinn"})
    itinerary.append({"day_range": f"Day {start_day_tallinn_val + duration_tallinn}", "place": "Tallinn"})
    itinerary.append({"day_range": f"Day {start_day_tallinn_val + duration_tallinn}", "place": "Stockholm"})

    itinerary.append({"day_range": f"Day {start_day_stockholm_val+1}-{start_day_stockholm_val + duration_stockholm}", "place": "Stockholm"})

    # Print the itinerary
    print({"itinerary": itinerary})
else:
    print("No solution found")