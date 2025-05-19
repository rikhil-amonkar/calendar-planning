import json

# Input parameters (all durations in days, and fixed overall duration)
total_days = 15

# Required stays in each city
required_madrid = 7    # Also needed for the annual Madrid show (days 1-7)
required_paris = 6
required_bucharest = 2  # Also visit relatives between day 14 and day 15
required_seville = 3

# Flight connectivity (for reference, not used in calculation directly):
# Available direct flights:
#   Madrid <-> Paris, Madrid <-> Seville, Madrid <-> Bucharest,
#   Paris <-> Bucharest, Seville <-> Paris

# Based on the constraints and overlapping flight-days,
# we determine the following itinerary:

# 1. Madrid must cover days 1 to 7 (annual show)
#    Even if a flight occurs on day 7, that day counts for both boarding and arrival.
madrid_start = 1
madrid_end = 7  # 7 days in Madrid

# 2. We want to leave Madrid and go to Seville.
#    We plan the flight from Madrid -> Seville on day 7.
#    That makes day 7 count for both Madrid and Seville.
seville_start = 7
# We need a total of 3 days in Seville. With day 7 counting,
# we then stay in Seville on day 8.
# To complete the 3 days, we fly from Seville -> Paris on day 9.
seville_end = 9  # (Days 7, 8, and 9 count as Seville)

# 3. Now we need Paris for 6 days.
#    We arrive in Paris on day 9 (flight from Seville -> Paris on day 9; day 9 counts for both cities)
paris_start = 9
# To accumulate 6 days in Paris, we count days: 9, 10, 11, 12, 13, 14.
# So we take the flight from Paris -> Bucharest on day 14.
paris_end = 14

# 4. Finally, Bucharest must be visited for 2 days and specifically for visiting relatives 
#    between day 14 and day 15.
#    We fly from Paris -> Bucharest on day 14 (day 14 counts for both),
#    then remain in Bucharest on day 15.
bucharest_start = 14
bucharest_end = 15

# Verify durations with overlapping rule:
# Madrid: days 1 through 7 -> 7 days.
# Seville: days 7, 8, 9 -> 3 days.
# Paris: days 9, 10, 11, 12, 13, 14 -> 6 days.
# Bucharest: days 14, 15 -> 2 days.
# Total trip spans from day 1 to day 15.

itinerary = [
    {"day_range": f"{madrid_start}-{madrid_end}", "place": "Madrid"},
    {"day_range": f"{seville_start}-{seville_end}", "place": "Seville"},
    {"day_range": f"{paris_start}-{paris_end}", "place": "Paris"},
    {"day_range": f"{bucharest_start}-{bucharest_end}", "place": "Bucharest"}
]

# Output the itinerary as a JSON-formatted dictionary.
print(json.dumps(itinerary, indent=2))