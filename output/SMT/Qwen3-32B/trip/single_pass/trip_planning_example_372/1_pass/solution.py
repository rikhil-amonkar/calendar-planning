from z3 import *
import json

# Define the cities and their required stay durations
cities = ['Madrid', 'Seville', 'Porto', 'Stuttgart']
stay_days = {
    'Madrid': 4,
    'Seville': 2,
    'Porto': 3,
    'Stuttgart': 7
}

# Valid direct flight pairs
direct_flights = {
    ('Madrid', 'Seville'),
    ('Madrid', 'Porto'),
    ('Seville', 'Porto'),
    ('Porto', 'Stuttgart')
}

# Sequence of cities with direct flights
sequence = ['Madrid', 'Seville', 'Porto', 'Stuttgart']

# Verify that all consecutive city pairs in the sequence have direct flights
for i in range(len(sequence) - 1):
    c1, c2 = sequence[i], sequence[i+1]
    if (c1, c2) not in direct_flights:
        print("Invalid sequence: No direct flight between", c1, "and", c2)
        exit()

# Define variables for start days
s_seville = Int('s_seville')
s_porto = Int('s_porto')
s_stuttgart = Int('s_stuttgart')

# Start day of Madrid is fixed at 1
s_madrid = 1

# Initialize Z3 solver
solver = Solver()

# Constraint: Start days are increasing
solver.add(s_seville > s_madrid)
solver.add(s_porto > s_seville)
solver.add(s_stuttgart > s_porto)

# Number of days in each city
# Madrid: s_seville - s_madrid + 1 == 4
solver.add(s_seville - s_madrid + 1 == stay_days['Madrid'])

# Seville: s_porto - s_seville + 1 == 2
solver.add(s_porto - s_seville + 1 == stay_days['Seville'])

# Porto: s_stuttgart - s_porto + 1 == 3
solver.add(s_stuttgart - s_porto + 1 == stay_days['Porto'])

# Stuttgart: 13 - s_stuttgart + 1 == 7
solver.add(13 - s_stuttgart + 1 == stay_days['Stuttgart'])

# Solve
if solver.check() == sat:
    model = solver.model()
    s_seville_val = model[s_seville].as_long()
    s_porto_val = model[s_porto].as_long()
    s_stuttgart_val = model[s_stuttgart].as_long()

    # Build the itinerary
    itinerary = []

    # Madrid: from s_madrid to s_seville - 1
    for day in range(s_madrid, s_seville_val):
        itinerary.append({"day": day, "city": "Madrid"})

    # Seville: from s_seville to s_porto - 1
    for day in range(s_seville_val, s_porto_val):
        itinerary.append({"day": day, "city": "Seville"})

    # Porto: from s_porto to s_stuttgart - 1
    for day in range(s_porto_val, s_stuttgart_val):
        itinerary.append({"day": day, "city": "Porto"})

    # Stuttgart: from s_stuttgart to 13
    for day in range(s_stuttgart_val, 14):
        itinerary.append({"day": day, "city": "Stuttgart"})

    # Output the result in JSON format
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")