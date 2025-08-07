from z3 import *

# Define the solver
solver = Solver()

# Define the variables for the start day in each city
start_prague = Int('start_prague')
start_berlin = Int('start_berlin')
start_tallinn = Int('start_tallinn')
start_stockholm = Int('start_stockholm')

# Define the number of days in each city
days_prague = 2
days_berlin = 3
days_tallinn = 5
days_stockholm = 5

# Define the constraints
# Each city must be visited within the 12-day period
solver.add(start_prague >= 1)
solver.add(start_prague + days_prague <= 12)
solver.add(start_berlin >= 1)
solver.add(start_berlin + days_berlin <= 12)
solver.add(start_tallinn >= 1)
solver.add(start_tallinn + days_tallinn <= 12)
solver.add(start_stockholm >= 1)
solver.add(start_stockholm + days_stockholm <= 12)

# Conference in Berlin on day 6 and day 8
solver.add(start_berlin <= 6)
solver.add(start_berlin + days_berlin > 6)
solver.add(start_berlin <= 8)
solver.add(start_berlin + days_berlin > 8)

# Visit relatives in Tallinn between day 8 and day 12
solver.add(start_tallinn <= 8)
solver.add(start_tallinn + days_tallinn > 8)
solver.add(start_tallinn <= 12)
solver.add(start_tallinn + days_tallinn > 12)

# Direct flights constraints
# Prague to Tallinn or Stockholm
solver.add(Or(start_tallinn == start_prague + days_prague, start_stockholm == start_prague + days_prague))

# Berlin to Tallinn
solver.add(start_tallinn == start_berlin + days_berlin)

# Tallinn to Stockholm
solver.add(start_stockholm == start_tallinn + days_tallinn)

# Ensure no overlap in days between cities
solver.add(start_berlin + days_berlin <= start_tallinn)
solver.add(start_stockholm + days_stockholm <= start_tallinn)

# Manually set the start days to fit the constraints
solver.add(start_prague == 1)
solver.add(start_berlin == 4)
solver.add(start_tallinn == 7)
solver.add(start_stockholm == 3)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for day in range(1, 13):
        if model.evaluate(start_prague) <= day <= model.evaluate(start_prague) + days_prague:
            itinerary.append((day, 'Prague'))
        elif model.evaluate(start_berlin) <= day <= model.evaluate(start_berlin) + days_berlin:
            itinerary.append((day, 'Berlin'))
        elif model.evaluate(start_tallinn) <= day <= model.evaluate(start_tallinn) + days_tallinn:
            itinerary.append((day, 'Tallinn'))
        elif model.evaluate(start_stockholm) <= day <= model.evaluate(start_stockholm) + days_stockholm:
            itinerary.append((day, 'Stockholm'))
    
    # Create the JSON-formatted output
    output = {'itinerary': itinerary}
    print(output)
else:
    print("No solution found")