from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_florence = Int('days_florence')
days_barcelona = Int('days_barcelona')
days_helsinki = Int('days_helsinki')

# Constraints for days spent
solver.add(days_florence == 6)  # Spend 6 days in Florence
solver.add(days_barcelona == 5)  # Spend 5 days in Barcelona
solver.add(days_helsinki == 5)   # Spend 5 days in Helsinki

# Total days constraint
solver.add(days_florence + days_barcelona + days_helsinki == 14)

# Constraints for visiting friend
# Florence is visited between days 9 and 14
# Which means the 1st day after spending 6 days in Florence should be day 9 or later.
# Florence can be visited from day 1 to day 6, so we'll need to decide the start day
start_barcelona = 6
start_helsinki = 11  # After Barcelona

# Specify a plan considering direct flights between the cities:
# Possible trip orderings while ensuring direct flight conditions:
# Florence (F) <-> Barcelona (B) <-> Helsinki (H)
plan = [
    'F' * days_florence,
    'B' * days_barcelona,
    'H' * days_helsinki
]

# Create the trip plan; must start and end within 14 days
trip = ''.join(plan)

# The trip plan must count for direct flights while ensuring meeting constraints.
# Find a valid plan satisfying trip order
valid_trip = ""

if solver.check() == sat:
    # Get the values from the solver
    days_florence_val = solver.model()[days_florence].as_long()
    days_barcelona_val = solver.model()[days_barcelona].as_long()
    days_helsinki_val = solver.model()[days_helsinki].as_long()
    
    valid_trip = f"Spend {days_florence_val} days in Florence, {days_barcelona_val} days in Barcelona, and {days_helsinki_val} days in Helsinki."
else:
    valid_trip = "No valid trip found."

print(valid_trip)