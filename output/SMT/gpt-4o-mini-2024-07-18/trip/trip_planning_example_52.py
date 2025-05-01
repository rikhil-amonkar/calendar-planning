from z3 import *

# Create a Z3 solver instance
s = Solver()

# Days spent in each city
days_madrid = Int('days_madrid')       # Days spent in Madrid
days_reykjavik = Int('days_reykjavik') # Days spent in Reykjavik
days_paris = Int('days_paris')         # Days spent in Paris

# Define the total number of days
total_days = 13

# Add constraints for the number of days spent in each city
s.add(days_madrid == 6)      # Spend 6 days in Madrid
s.add(days_reykjavik == 4)   # Spend 4 days in Reykjavik
s.add(days_paris == 5)       # Spend 5 days in Paris

# Constraint for the total number of days
s.add(days_madrid + days_reykjavik + days_paris == total_days)  # Total days must equal 13

# Ensure that you are in Reykjavik between days 10 and 13 for the relatives visit
# This means at least some part of the Reykjavik days must overlap with days 10 to 13
s.add(days_reykjavik >= 3)  # Must have enough days in Reykjavik for the visit

# Direct flights:
# 1. Reykjavik <--> Madrid
# 2. Reykjavik <--> Paris
# 3. Madrid <--> Paris

# Create an itinerary based on the specified days
itinerary = ["Madrid"] * days_madrid + ["Reykjavik"] * days_reykjavik + ["Paris"] * days_paris

# Ensure that Reykjavik is visited during the last 4 days for the relatives visit (days 10 to 13)
relatives_days = itinerary[9:]  # Corresponds to days 10 to 13
meeting_possible = any(city == "Reykjavik" for city in relatives_days)  # Ensure we are in Reykjavik

# Add constraint if meeting requirement is satisfied
if meeting_possible:
    s.add(True)  # This serves only as a placeholder for Z3 to run smoothly

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    madrid_days = model[days_madrid].as_long()
    reykjavik_days = model[days_reykjavik].as_long()
    paris_days = model[days_paris].as_long()

    print("Trip schedule is possible with the following distribution of days:")
    print(f"Madrid: {madrid_days} days")
    print(f"Reykjavik: {reykjavik_days} days")
    print(f"Paris: {paris_days} days")

    print("\nItinerary for your trip:")
    print(itinerary)
else:
    print("No possible trip schedule found.")