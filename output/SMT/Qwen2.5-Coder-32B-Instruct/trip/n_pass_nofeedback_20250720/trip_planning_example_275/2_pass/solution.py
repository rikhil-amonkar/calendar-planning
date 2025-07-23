from z3 import *

# Define the solver
solver = Solver()

# Define the variables for the start day of each city visit
start_split = Int('start_split')
start_vilnius = Int('start_vilnius')
start_madrid = Int('start_madrid')
start_santorini = Int('start_santorini')

# Define the duration of stay in each city
duration_split = 5
duration_vilnius = 4
duration_madrid = 6
duration_santorini = 2

# Define the constraints
# 1. The total trip duration is 14 days
solver.add(start_split + duration_split <= 15)  # Split visit must end by day 14
solver.add(start_vilnius + duration_vilnius <= 15)  # Vilnius visit must end by day 14
solver.add(start_madrid + duration_madrid <= 15)  # Madrid visit must end by day 14
solver.add(start_santorini + duration_santorini <= 15)  # Santorini visit must end by day 14

# 2. Specific requirements for Santorini
solver.add(start_santorini == 13)  # Must be in Santorini on day 13 and 14

# 3. Flight connections
# Split to Madrid: start_madrid must be between start_split + duration_split - 1 and start_split + duration_split
solver.add(start_madrid >= start_split + duration_split - 1)
solver.add(start_madrid <= start_split + duration_split)

# Vilnius to Split: start_split must be between start_vilnius + duration_vilnius - 1 and start_vilnius + duration_vilnius
solver.add(start_split >= start_vilnius + duration_vilnius - 1)
solver.add(start_split <= start_vilnius + duration_vilnius)

# Madrid to Santorini: start_santorini must be between start_madrid + duration_madrid - 1 and start_madrid + duration_madrid
solver.add(start_santorini >= start_madrid + duration_madrid - 1)
solver.add(start_santorini <= start_madrid + duration_madrid)

# 4. All start days must be positive
solver.add(start_split >= 1)
solver.add(start_vilnius >= 1)
solver.add(start_madrid >= 1)
solver.add(start_santorini >= 1)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for day in range(1, 15):
        place = If(And(model.evaluate(start_vilnius) <= day, day <= model.evaluate(start_vilnius) + duration_vilnius - 1),
                   "Vilnius",
                   If(And(model.evaluate(start_split) <= day, day <= model.evaluate(start_split) + duration_split - 1),
                      "Split",
                      If(And(model.evaluate(start_madrid) <= day, day <= model.evaluate(start_madrid) + duration_madrid - 1),
                         "Madrid",
                         If(And(model.evaluate(start_santorini) <= day, day <= model.evaluate(start_santorini) + duration_santorini - 1),
                            "Santorini",
                            "Unknown"))))
        itinerary.append({"day": day, "place": place.as_string()})
    result = {"itinerary": itinerary}
    print(result)
else:
    print("No solution found")