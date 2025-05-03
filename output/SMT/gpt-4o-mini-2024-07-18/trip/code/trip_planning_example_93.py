from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_dubrovnik = Int('days_dubrovnik')
days_dublin = Int('days_dublin')
days_seville = Int('days_seville')

# Constraints for the number of days spent in each city
solver.add(days_dubrovnik == 2)              # Spend 2 days in Dubrovnik
solver.add(days_dublin == 4)                  # Spend 4 days in Dublin
solver.add(days_seville == 4)                 # Spend 4 days in Seville (adjusted)

# Total days constraint
solver.add(days_dubrovnik + days_dublin + days_seville == 10)

# Requirements for attending the wedding in Dubrovnik must fall on day 9 and day 10
# The days in Dubrovnik must occur at the end of the trip to fit the wedding.

# Check for valid combinations
if solver.check() == sat:
    # If a valid solution is found, extract the values
    days_dubrovnik_val = solver.model()[days_dubrovnik].as_long()
    days_dublin_val = solver.model()[days_dublin].as_long()
    days_seville_val = solver.model()[days_seville].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_dubrovnik_val} days in Dubrovnik, "
        f"{days_dublin_val} days in Dublin, "
        f"{days_seville_val} days in Seville."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)