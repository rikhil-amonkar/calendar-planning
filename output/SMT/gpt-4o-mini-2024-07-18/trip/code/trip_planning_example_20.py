from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_istanbul = Int('days_istanbul')
days_budapest = Int('days_budapest')
days_dubrovnik = Int('days_dubrovnik')

# Constraints for days spent in each city
solver.add(days_istanbul == 5)            # Spend 5 days in Istanbul
solver.add(days_budapest == 6)            # Spend 6 days in Budapest
solver.add(days_dubrovnik == 3)           # Spend 3 days in Dubrovnik

# Total days constraint
solver.add(days_istanbul + days_budapest + days_dubrovnik == 12)

# Check for possible combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_istanbul_val = solver.model()[days_istanbul].as_long()
    days_budapest_val = solver.model()[days_budapest].as_long()
    days_dubrovnik_val = solver.model()[days_dubrovnik].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_istanbul_val} days in Istanbul, "
        f"{days_budapest_val} days in Budapest, "
        f"{days_dubrovnik_val} days in Dubrovnik."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)