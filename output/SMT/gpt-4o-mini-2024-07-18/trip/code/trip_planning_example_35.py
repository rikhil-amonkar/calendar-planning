from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_bucharest = Int('days_bucharest')
days_zurich = Int('days_zurich')
days_dubrovnik = Int('days_dubrovnik')

# Constraints for days spent in each city
solver.add(days_bucharest == 3)          # Spend 3 days in Bucharest
solver.add(days_zurich == 2)              # Spend 2 days in Zurich
solver.add(days_dubrovnik == 7)           # Spend 7 days in Dubrovnik

# Total days constraint
solver.add(days_bucharest + days_zurich + days_dubrovnik == 10)

# Constraint for visiting relatives in Dubrovnik (must be between day 4 and day 10)
# This means you need to be in Dubrovnik from day 4 to day 10, which overlaps
# perfectly with the total of 7 days spent there.

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_bucharest_val = solver.model()[days_bucharest].as_long()
    days_zurich_val = solver.model()[days_zurich].as_long()
    days_dubrovnik_val = solver.model()[days_dubrovnik].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_bucharest_val} days in Bucharest, "
        f"{days_zurich_val} days in Zurich, "
        f"{days_dubrovnik_val} days in Dubrovnik."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)