from z3 import *

# Create a Z3 solver instance
s = Solver()

# Days spent in each city
days_santorini = Int('days_santorini')  # Days spent in Santorini
days_krakow = Int('days_krakow')        # Days spent in Krakow
days_london = Int('days_london')         # Days spent in London

# Define the total number of days
total_days = 14

# Add constraints for the number of days spent in each city
s.add(days_santorini == 6)  # Spend 6 days in Santorini
s.add(days_krakow == 5)      # Spend 5 days in Krakow
s.add(days_london == 5)       # Spend 5 days in London

# Constraint for the total number of days
s.add(days_santorini + days_krakow + days_london == total_days)  # Total days must equal 14

# Ensure the annual show in Santorini is attended between days 1 and 6
# This means at least 6 days in Santorini are needed for the show.
s.add(days_santorini >= 6)  # Must have enough days in Santorini for the show

# Since there are direct flights:
# 1. Santorini <--> London
# 2. Krakow <--> London

# Create an itinerary based on the specified days
itinerary = ["Santorini"] * days_santorini + ["Krakow"] * days_krakow + ["London"] * days_london

# Ensure that Santorini is visited during the first 6 days for the show
show_days = itinerary[:6]  # Check days 1 to 6
show_possible = any(city == "Santorini" for city in show_days)  # Check if Santorini is included in first 6 days

# Check if the show condition is met
if show_possible:
    s.add(True)  # Just a placeholder for Z3 validation

# Check for satisfiability
if s.check() == sat:
    model = s.model()
    santorini_days = model[days_santorini].as_long()
    krakow_days = model[days_krakow].as_long()
    london_days = model[days_london].as_long()

    print("Trip schedule is possible with the following distribution of days:")
    print(f"Santorini: {santorini_days} days")
    print(f"Krakow: {krakow_days} days")
    print(f"London: {london_days} days")

    print("\nItinerary for your trip:")
    print(itinerary)
else:
    print("No possible trip schedule found.")