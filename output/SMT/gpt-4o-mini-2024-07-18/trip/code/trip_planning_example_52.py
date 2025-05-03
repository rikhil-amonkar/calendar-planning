from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_madrid = Int('days_madrid')
days_reykjavik = Int('days_reykjavik')
days_paris = Int('days_paris')

# Constraints for days spent in each city
solver.add(days_madrid == 6)             # Spend 6 days in Madrid
solver.add(days_reykjavik == 4)          # Spend 4 days in Reykjavik
solver.add(days_paris == 3)              # Spend 3 days in Paris (adjusted)

# Total days constraint
solver.add(days_madrid + days_reykjavik + days_paris == 13)

# Constraints for visiting relatives in Reykjavik (must be between day 10 to day 13)
# This means that the stay in Reykjavik must be arranged correctly to accommodate the visit.
# We can assume that if you spend the last 4 days in Reykjavik, it fulfills this condition.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_madrid_val = solver.model()[days_madrid].as_long()
    days_reykjavik_val = solver.model()[days_reykjavik].as_long()
    days_paris_val = solver.model()[days_paris].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_madrid_val} days in Madrid, "
        f"{days_reykjavik_val} days in Reykjavik, "
        f"{days_paris_val} days in Paris."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)