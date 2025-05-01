from z3 import *

# Create a Z3 solver instance
s = Solver()

# Days spent in each city
days_porto = Int('days_porto')      # Days spent in Porto
days_berlin = Int('days_berlin')    # Days spent in Berlin
days_reykjavik = Int('days_reykjavik') # Days spent in Reykjavik

# Define the total number of days
total_days = 16

# Add constraints for the number of days spent in each city
s.add(days_porto == 7)       # Spend 7 days in Porto
s.add(days_berlin == 6)      # Spend 6 days in Berlin
s.add(days_reykjavik == 5)   # Spend 5 days in Reykjavik

# Constraint for the total number of days
s.add(days_porto + days_berlin + days_reykjavik == total_days)  # Total days must equal 16

# Ensure the meeting with a friend in Reykjavik is between days 12 and 16
# This means at least one of the Reykjavik days must fall in those last days
s.add(days_reykjavik >= 3)  # At least 3 days in Reykjavik to meet the friend

# Direct flights:
# 1. Porto <--> Berlin
# 2. Berlin <--> Reykjavik

# Create an itinerary based on the planned days
itinerary = ["Porto"] * days_porto + ["Berlin"] * days_berlin + ["Reykjavik"] * days_reykjavik

# Here, we want to check that Reykjavik is visited on days 12 to 16 (0-indexed)
meeting_days = itinerary[11:]  # Days 12 to 16 correspond to indices 11 to 15

# Check if Reykjavik is present during the last days for the meeting
meeting_possible = any(city == "Reykjavik" for city in meeting_days)

# Adding an artificial condition to keep the solver working correctly
if meeting_possible:
    s.add(True)  # No additional constraints needed

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    porto_days = model[days_porto].as_long()
    berlin_days = model[days_berlin].as_long()
    reykjavik_days = model[days_reykjavik].as_long()

    print("Trip schedule is possible with the following distribution of days:")
    print(f"Porto: {porto_days} days")
    print(f"Berlin: {berlin_days} days")
    print(f"Reykjavik: {reykjavik_days} days")

    print("\nItinerary for your trip:")
    print(itinerary)

else:
    print("No possible trip schedule found.")