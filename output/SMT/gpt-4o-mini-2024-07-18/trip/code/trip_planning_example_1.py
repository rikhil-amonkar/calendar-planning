from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_split = Int('days_split')
days_manchester = Int('days_manchester')
days_riga = Int('days_riga')

# Constraints for days spent in each city
solver.add(days_split == 6)           # Spend 6 days in Split
solver.add(days_manchester == 4)      # Spend 4 days in Manchester
solver.add(days_riga == 7)             # Spend 7 days in Riga

# Total days constraint
solver.add(days_split + days_manchester + days_riga == 15)

# Since we know the flight paths, let's validate travel:
# The travel must be valid considering the direct connections available:
# - Manchester <-> Split
# - Riga <-> Manchester
# We can start at any city, but must follow the direct routes between them.

# For possible trip plans, we need to ensure order:
# A valid ordering could be (Riga -> Manchester -> Split) or any variant
# Plan creation: Sheffield -> Manchester -> Split (or any permutation respecting direct flights)

# To find a valid trip sequence, we can simulate possible plans
valid_trip = ""

if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_split_val = solver.model()[days_split].as_long()
    days_manchester_val = solver.model()[days_manchester].as_long()
    days_riga_val = solver.model()[days_riga].as_long()
    
    # Create a trip plan:
    valid_trip = (
        f"Spend {days_split_val} days in Split, "
        f"{days_manchester_val} days in Manchester, "
        f"and {days_riga_val} days in Riga."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)