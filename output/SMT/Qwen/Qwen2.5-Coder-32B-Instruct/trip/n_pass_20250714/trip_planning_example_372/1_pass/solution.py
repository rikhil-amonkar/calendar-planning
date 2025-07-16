from z3 import *

# Define the solver
solver = Solver()

# Define the variables for the start day of each city
start_seville = Int('start_seville')
start_stuttgart = Int('start_stuttgart')
start_porto = Int('start_porto')
start_madrid = Int('start_madrid')

# Define the duration of stay in each city
duration_seville = 2
duration_stuttgart = 7
duration_porto = 3
duration_madrid = 4

# Define the constraints
# Stay in Seville for 2 days
solver.add(start_seville >= 1)
solver.add(start_seville + duration_seville <= 13)

# Stay in Stuttgart for 7 days, including days 7 and 13 for the conference
solver.add(start_stuttgart == 7)  # Must start on day 7 for the conference
solver.add(start_stuttgart + duration_stuttgart <= 13)

# Stay in Porto for 3 days
solver.add(start_porto >= 1)
solver.add(start_porto + duration_porto <= 13)

# Stay in Madrid for 4 days, including days 1-4 to visit relatives
solver.add(start_madrid == 1)  # Must start on day 1 to visit relatives
solver.add(start_madrid + duration_madrid <= 13)

# Ensure no overlap between stays in different cities
solver.add(Or(start_seville + duration_seville <= start_stuttgart,
              start_stuttgart + duration_stuttgart <= start_seville))

solver.add(Or(start_seville + duration_seville <= start_porto,
              start_porto + duration_porto <= start_seville))

solver.add(Or(start_seville + duration_seville <= start_madrid,
              start_madrid + duration_madrid <= start_seville))

solver.add(Or(start_stuttgart + duration_stuttgart <= start_porto,
              start_porto + duration_porto <= start_stuttgart))

solver.add(Or(start_stuttgart + duration_stuttgart <= start_madrid,
              start_madrid + duration_madrid <= start_stuttgart))

solver.add(Or(start_porto + duration_porto <= start_madrid,
              start_madrid + duration_madrid <= start_porto))

# Ensure valid transitions between cities using direct flights
# Possible transitions: Porto <-> Stuttgart, Seville <-> Porto, Madrid <-> Porto, Madrid <-> Seville
# We need to add constraints to ensure that transitions happen on the correct days

# Transition from Seville to Porto or Madrid
transition_seville_to_porto_or_madrid = Or(
    And(start_seville + duration_seville == start_porto - 1),
    And(start_seville + duration_seville == start_madrid - 1)
)
solver.add(transition_seville_to_porto_or_madrid)

# Transition from Porto to Seville or Madrid or Stuttgart
transition_porto_to_seville_or_madrid_or_stuttgart = Or(
    And(start_porto + duration_porto == start_seville - 1),
    And(start_porto + duration_porto == start_madrid - 1),
    And(start_porto + duration_porto == start_stuttgart - 1)
)
solver.add(transition_porto_to_seville_or_madrid_or_stuttgart)

# Transition from Madrid to Seville or Porto
transition_madrid_to_seville_or_porto = Or(
    And(start_madrid + duration_madrid == start_seville - 1),
    And(start_madrid + duration_madrid == start_porto - 1)
)
solver.add(transition_madrid_to_seville_or_porto)

# Check if the solution is feasible
if solver.check() == sat:
    model = solver.model()
    print("Solution found:")
    itinerary = []
    
    # Add Seville days
    seville_start = model[start_seville].as_long()
    itinerary.append({"day_range": f"Day {seville_start}-{seville_start + duration_seville - 1}", "place": "Seville"})
    itinerary.append({"day_range": f"Day {seville_start + duration_seville - 1}", "place": "Seville"})
    
    # Add Stuttgart days
    stuttgart_start = model[start_stuttgart].as_long()
    itinerary.append({"day_range": f"Day {stuttgart_start}-{stuttgart_start + duration_stuttgart - 1}", "place": "Stuttgart"})
    itinerary.append({"day_range": f"Day {stuttgart_start + duration_stuttgart - 1}", "place": "Stuttgart"})
    
    # Add Porto days
    porto_start = model[start_porto].as_long()
    itinerary.append({"day_range": f"Day {porto_start}-{porto_start + duration_porto - 1}", "place": "Porto"})
    itinerary.append({"day_range": f"Day {porto_start + duration_porto - 1}", "place": "Porto"})
    
    # Add Madrid days
    madrid_start = model[start_madrid].as_long()
    itinerary.append({"day_range": f"Day {madrid_start}-{madrid_start + duration_madrid - 1}", "place": "Madrid"})
    itinerary.append({"day_range": f"Day {madrid_start + duration_madrid - 1}", "place": "Madrid"})
    
    # Sort itinerary by day range
    itinerary.sort(key=lambda x: int(x["day_range"].split('-')[0].split()[1]))
    
    # Print the itinerary
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")