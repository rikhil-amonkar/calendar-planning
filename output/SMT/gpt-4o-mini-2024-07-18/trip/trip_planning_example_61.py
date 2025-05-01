from z3 import *

# Create a Z3 solver instance
s = Solver()

# Days spent in each city
days_zurich = Int('days_zurich')   # Days spent in Zurich
days_bucharest = Int('days_bucharest') # Days spent in Bucharest
days_helsinki = Int('days_helsinki')     # Days spent in Helsinki

# Define the total number of days
total_days = 13

# Add constraints for the number of days spent in each city
s.add(days_zurich == 7)      # Spend 7 days in Zurich
s.add(days_bucharest == 3)     # Spend 3 days in Bucharest
s.add(days_helsinki == 5)      # Spend 5 days in Helsinki

# Constraint for the total number of days
s.add(days_zurich + days_bucharest + days_helsinki == total_days)  # Total days must equal 13

# Ensure meeting friends in Helsinki occurs between days 1 and 5
# This means at least 1 of the Helsinki days should be in those days
s.add(days_helsinki >= 4)  # At least 4 days in Helsinki to accommodate the meeting

# Since there are direct flights:
# 1. Zurich <--> Bucharest
# 2. Zurich <--> Helsinki

# Create an itinerary based on the specified days
itinerary = ["Zurich"] * days_zurich + ["Bucharest"] * days_bucharest + ["Helsinki"] * days_helsinki

# Ensure that Helsinki is visited during the days 1 to 5 for meeting friends
meeting_days = itinerary[:5]  # Checking the first 5 days for the trip
meeting_possible = any(city == "Helsinki" for city in meeting_days)  # Ensure we have Helsinki

# If the meeting condition is satisfied
if meeting_possible:
    s.add(True)  # Placeholder to satisfy Z3

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    zurich_days = model[days_zurich].as_long()
    bucharest_days = model[days_bucharest].as_long()
    helsinki_days = model[days_helsinki].as_long()

    print("Trip schedule is possible with the following distribution of days:")
    print(f"Zurich: {zurich_days} days")
    print(f"Bucharest: {bucharest_days} days")
    print(f"Helsinki: {helsinki_days} days")

    print("\nItinerary for your trip:")
    print(itinerary)
else:
    print("No possible trip schedule found.")