from z3 import *

# Create the solver instance
solver = Solver()

# Variables for days spent in each city
days_tallinn = Int('days_tallinn')
days_seville = Int('days_seville')
days_munich = Int('days_munich')

# Constraints for days spent in each city
solver.add(days_tallinn == 2)        # Spend 2 days in Tallinn
solver.add(days_seville == 7)        # Spend 7 days in Seville
solver.add(days_munich == 5)         # Spend 5 days in Munich

# Total days constraint
solver.add(days_tallinn + days_seville + days_munich == 12)

# Constraints for meeting in Tallinn (must be on day 11 or 12)
# Since we are spending 2 days in Tallinn, it can only occupy days 11 and 12.
# That means we must arrive in Tallinn by day 11, thus no stays in Tallinn before that.

# Let's also think about the possible sequential flow of the trip:

# Possible trip order considering the direct flight paths:
# Seville <-> Munich and Munich <-> Tallinn.

# We can start with Seville then go to Munich and finally to Tallinn.
# All travels must be valid and connected.

# Check if a valid trip exists
if solver.check() == sat:
    # Take the values from the model if there's a valid solution
    days_tallinn_val = solver.model()[days_tallinn].as_long()
    days_seville_val = solver.model()[days_seville].as_long()
    days_munich_val = solver.model()[days_munich].as_long()
    
    # Create a trip plan description
    valid_trip = (
        f"Spend {days_tallinn_val} days in Tallinn, "
        f"{days_seville_val} days in Seville, "
        f"and {days_munich_val} days in Munich."
    )
else:
    valid_trip = "No valid trip plan found."

print(valid_trip)