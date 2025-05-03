from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_reykjavik = Int('days_reykjavik')
days_vienna = Int('days_vienna')
days_venice = Int('days_venice')

# Constraints for days spent in each city
solver.add(days_reykjavik == 2)       # Spend 2 days in Reykjavik
solver.add(days_vienna == 7)           # Spend 7 days in Vienna
solver.add(days_venice == 4)           # Spend 4 days in Venice

# Total days constraint
solver.add(days_reykjavik + days_vienna + days_venice == 11)

# Constraints for the wedding in Venice
# Venice days must be between day 8 and day 11
# This means that since Venice is 4 days, it should occupy days 8 to 11
# Hence, it can only start being planned on Day 8 or 9 if we think in terms of planning
# Number of days in Vienna can fall up to day 7.
wedding_days = 3  # 4 - (8 - 5) = Days from Venice where wedding is on day 9 to 11

# Encode the wedding constraints
# This implies Venice can only be visited at the end
solver.add(And(days_vienna + 4 >= 8, days_vienna <= 7))  # V day 8 or later and stays till 11

# Possible trip orders with direct flights:
# Start can be Reykjavik -> Vienna 
# Then travel from Vienna -> Venice

if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_reykjavik_val = solver.model()[days_reykjavik].as_long()
    days_vienna_val = solver.model()[days_vienna].as_long()
    days_venice_val = solver.model()[days_venice].as_long()
    
    # Create a trip plan:
    valid_trip = (
        f"Spend {days_reykjavik_val} days in Reykjavik, "
        f"{days_vienna_val} days in Vienna, "
        f"and {days_venice_val} days in Venice."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)