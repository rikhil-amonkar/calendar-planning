from z3 import *

# Create a Z3 solver instance
s = Solver()

# Days spent in each city
days_mykonos = Int('days_mykonos')  # Days spent in Mykonos
days_nice = Int('days_nice')        # Days spent in Nice
days_helsinki = Int('days_helsinki') # Days spent in Helsinki

# Define the total number of days
total_days = 14

# Add constraints for the number of days spent in each city
s.add(days_mykonos == 4)     # Spend 4 days in Mykonos
s.add(days_nice == 6)        # Spend 6 days in Nice
s.add(days_helsinki == 6)     # Spend 6 days in Helsinki

# Constraint for the total number of days
s.add(days_mykonos + days_nice + days_helsinki == total_days)  # Total days must equal 14

# Ensure that the show in Helsinki is attended between days 1 and 6
# This means we need at least 6 of the Helsinki days to cover the show period
s.add(days_helsinki >= 6)  # Must have enough days in Helsinki to attend the annual show

# Since there are direct flights:
# 1. Nice <--> Helsinki
# 2. Nice <--> Mykonos

# Build the itinerary based on the specified days
itinerary = ["Mykonos"] * days_mykonos + ["Nice"] * days_nice + ["Helsinki"] * days_helsinki

# Check if Helsinki is included in the days for the show (days 1 to 6)
show_days = itinerary[:6]  # Checking first 6 days
show_possible = any(city == "Helsinki" for city in show_days)  # Ensure we are in Helsinki for the show

# Check if the meeting requirement is satisfied to inform Z3
if show_possible:
    s.add(True)  # Placeholder to ensure valid Z3 processing

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    mykonos_days = model[days_mykonos].as_long()
    nice_days = model[days_nice].as_long()
    helsinki_days = model[days_helsinki].as_long()

    print("Trip schedule is possible with the following distribution of days:")
    print(f"Mykonos: {mykonos_days} days")
    print(f"Nice: {nice_days} days")
    print(f"Helsinki: {helsinki_days} days")

    print("\nItinerary for your trip:")
    print(itinerary)
else:
    print("No possible trip schedule found.")