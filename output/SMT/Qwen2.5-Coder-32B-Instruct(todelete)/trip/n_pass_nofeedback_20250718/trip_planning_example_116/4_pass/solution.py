from z3 import *

# Define the solver
solver = Solver()

# Define the variables for the start day of each city
start_split = Int('start_split')
start_santorini = Int('start_santorini')
start_london = Int('start_london')

# Define the duration of stay in each city
duration_split = 6
duration_santorini = 7
duration_london = 7

# Define the total number of days
total_days = 18

# Constraints
# 1. The start day of each city must be non-negative
solver.add(start_split >= 1)
solver.add(start_santorini >= 1)
solver.add(start_london >= 1)

# 2. The end day of each city must be within the total number of days
solver.add(start_split + duration_split <= total_days)
solver.add(start_santorini + duration_santorini <= total_days)
solver.add(start_london + duration_london <= total_days)

# 3. You must attend the conference in Santorini on day 12 and day 18
solver.add(And(start_santorini <= 12, start_santorini + duration_santorini >= 13))
solver.add(And(start_santorini <= 18, start_santorini + duration_santorini >= 19))

# 4. You can only fly between cities with direct flights: London and Santorini, Split and London
#    This means the start day of one city must be the end day of another city plus one
#    We need to consider the specific order: Split -> London -> Santorini

# Case: Split -> London -> Santorini
solver.add(start_london == start_split + duration_split)
solver.add(start_santorini == start_london + duration_london)

if solver.check() == sat:
    model = solver.model()
    itinerary = [
        {"day_range": f"Day {model[start_split].as_long()}-{model[start_split].as_long() + duration_split - 1}", "place": "Split"},
        {"day_range": f"Day {model[start_london].as_long()}-{model[start_london].as_long() + duration_london - 1}", "place": "London"},
        {"day_range": f"Day {model[start_santorini].as_long()}-{model[start_santorini].as_long() + duration_santorini - 1}", "place": "Santorini"}
    ]
    print({"itinerary": itinerary})
else:
    print("No valid itinerary found")