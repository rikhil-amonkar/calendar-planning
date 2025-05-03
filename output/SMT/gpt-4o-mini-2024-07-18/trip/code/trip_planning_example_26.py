from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_porto = Int('days_porto')
days_berlin = Int('days_berlin')
days_reykjavik = Int('days_reykjavik')

# Constraints for days spent in each city
solver.add(days_porto == 7)             # Spend 7 days in Porto
solver.add(days_berlin == 6)            # Spend 6 days in Berlin
solver.add(days_reykjavik == 5)         # Spend 5 days in Reykjavik

# Total days constraint
solver.add(days_porto + days_berlin + days_reykjavik == 16)

# Constraints for meeting a friend in Reykjavik (must be between days 12 and 16)
# This means you need to schedule your trip such that you arrive in Reykjavik
# appropriately after spending time in the other two cities.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_porto_val = solver.model()[days_porto].as_long()
    days_berlin_val = solver.model()[days_berlin].as_long()
    days_reykjavik_val = solver.model()[days_reykjavik].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_porto_val} days in Porto, "
        f"{days_berlin_val} days in Berlin, "
        f"{days_reykjavik_val} days in Reykjavik."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)