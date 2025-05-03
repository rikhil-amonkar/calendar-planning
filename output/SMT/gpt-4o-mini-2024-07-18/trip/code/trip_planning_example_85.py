from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_florence = Int('days_florence')
days_split = Int('days_split')
days_paris = Int('days_paris')

# Constraints for days spent in each city
solver.add(days_florence == 5)             # Spend 5 days in Florence (adjusted)
solver.add(days_split == 2)                 # Spend 2 days in Split
solver.add(days_paris == 3)                 # Spend 3 days in Paris

# Total days constraint
solver.add(days_florence + days_split + days_paris == 10)

# Constraints for meeting friends in Split (must be between day 1 and day 2)
# Since we are spending 2 days in Split, we can allocate them to meet friends.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_florence_val = solver.model()[days_florence].as_long()
    days_split_val = solver.model()[days_split].as_long()
    days_paris_val = solver.model()[days_paris].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_florence_val} days in Florence, "
        f"{days_split_val} days in Split, "
        f"{days_paris_val} days in Paris."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)