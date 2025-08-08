#!/usr/bin/env python3
import json

# Trip constraints (input variables)
total_days = 10
durations = {
    "Krakow": 2,
    "Dubrovnik": 7,
    "Frankfurt": 3
}
wedding_window = (9, 10)  # Wedding in Krakow must occur between day 9 and day 10

# Available direct flights (bidirectional)
# Direct flights exist between Frankfurt and Krakow, and between Dubrovnik and Frankfurt.
direct_flights = {
    ("Frankfurt", "Krakow"),
    ("Krakow", "Frankfurt"),
    ("Dubrovnik", "Frankfurt"),
    ("Frankfurt", "Dubrovnik")
}

# The only valid ordering to visit all 3 cities (given the flight graph) is:
# Dubrovnik -> Frankfurt -> Krakow.
# We use flight-day overlaps to satisfy the total day count.
#
# Rule: If you fly from city A to city B on day X, then day X counts for both A and B.
#
# Let:
#   Dubrovnik stay be D days, Frankfurt stay be F days, Krakow stay be K days.
# Total days counted = D + F + K - (number of flights)
# We have 2 flights so:
#   Total = 7 + 3 + 2 - 2 = 10 days, which matches our itinerary.
#
# We schedule the flights on the last day of the previous stay so as to count the overlapping day.
#
# Dubrovnik: from Day 1 to Day 7
dubrovnik_start = 1
dubrovnik_end = dubrovnik_start + durations["Dubrovnik"] - 1  # 1 + 7 - 1 = 7

# Flight from Dubrovnik to Frankfurt on Day 7 (overlap)
frankfurt_start = dubrovnik_end  # Day 7 is in both Dubrovnik and Frankfurt
frankfurt_end = frankfurt_start + durations["Frankfurt"] - 1  # 7 + 3 - 1 = 9

# Flight from Frankfurt to Krakow on Day 9 (overlap)
krakow_start = frankfurt_end  # Day 9 is in both Frankfurt and Krakow
krakow_end = krakow_start + durations["Krakow"] - 1  # 9 + 2 - 1 = 10

# Check that the computed itinerary matches the total days constraint
assert krakow_end == total_days, "The itinerary does not match the total days constraint."

# Check that the wedding in Krakow is scheduled between day 9 and day 10.
# For instance, we choose day 9 (the overlap day) for the wedding in Krakow.
wedding_day = 9
assert krakow_start <= wedding_day <= krakow_end, "Wedding not scheduled in Krakow as required."

# Build the itinerary list with day-range mapping
itinerary = [
    {"day_range": f"Day {dubrovnik_start}-{dubrovnik_end}", "place": "Dubrovnik"},
    {"day_range": f"Day {frankfurt_start}-{frankfurt_end}", "place": "Frankfurt"},
    {"day_range": f"Day {krakow_start}-{krakow_end}", "place": "Krakow"}
]

# Output the result as a JSON-formatted dictionary
output = {"itinerary": itinerary}
print(json.dumps(output))