import json

# Define the trip constraints as input variables
# Each tuple: (city, required_days)
# Note: When transitioning between cities via direct flight,
# the day of flight counts as a day in both cities.
# Thus, the sum(required_days) - (# flights) should equal the total trip days.
total_trip_days = 18

# Cities with required durations:
# Mykonos must be visited for 4 days (and between day 15 and 18).
# Dubrovnik must be visited for 3 days (and must include days 2 to 4 for the annual show).
# Oslo 2 days (with friends meeting between day 1 and 2),
# Krakow 5 days, Vilnius 2 days, Helsinki 2 days, Madrid 5 days, Paris 2 days.
#
# We must arrange an order using only the given direct flight connections.
# The available direct flight connections (bidirectional) are:
# Oslo-Krakow, Oslo-Paris, Paris-Madrid, Helsinki-Vilnius, Oslo-Madrid, Oslo-Helsinki,
# Helsinki-Krakow, Dubrovnik-Helsinki, Dubrovnik-Madrid, Oslo-Dubrovnik, Krakow-Paris,
# Madrid-Mykonos, Oslo-Vilnius, Krakow-Vilnius, Helsinki-Paris, Vilnius-Paris, Helsinki-Madrid.
#
# After careful examination and ensuring that seasonal constraints are met,
# one viable ordering is as follows:
# 1. Oslo (2 days)      -> friends meet between day 1-2.
# 2. Dubrovnik (3 days)  -> flight from Oslo to Dubrovnik means day2 is common; also shows on days 2-4.
# 3. Helsinki (2 days)   -> flight from Dubrovnik to Helsinki (day4 common).
# 4. Krakow (5 days)     -> flight from Helsinki to Krakow (day5 common).
# 5. Vilnius (2 days)    -> flight from Krakow to Vilnius (day9 common).
# 6. Paris (2 days)      -> flight from Vilnius to Paris (day10 common).
# 7. Madrid (5 days)     -> flight from Paris to Madrid (day11 common).
# 8. Mykonos (4 days)    -> flight from Madrid to Mykonos (day15 common, and relatives visited within days 15-18).
#
# The direct flights used in this itinerary are:
# Oslo -> Dubrovnik, Dubrovnik -> Helsinki, Helsinki -> Krakow,
# Krakow -> Vilnius, Vilnius -> Paris, Paris -> Madrid, Madrid -> Mykonos.
# Each flight day is overlapped between the two cities.

itinerary_cities = [
    {"place": "Oslo", "required_days": 2},
    {"place": "Dubrovnik", "required_days": 3},
    {"place": "Helsinki", "required_days": 2},
    {"place": "Krakow", "required_days": 5},
    {"place": "Vilnius", "required_days": 2},
    {"place": "Paris", "required_days": 2},
    {"place": "Madrid", "required_days": 5},
    {"place": "Mykonos", "required_days": 4}
]

# Calculate the itinerary schedule using the overlapping rules.
# Let day_i and day_j be computed as:
# For the first city:
#    start_day = 1
#    end_day = start_day + required_days - 1
# For each subsequent city:
#    start_day = previous city's end_day (flight day overlap)
#    end_day = start_day + required_days - 1
#
# This ensures that each flight day contributes to both cities and the total days add up.

schedule = []
current_day = 1
for city in itinerary_cities:
    start_day = current_day
    end_day = start_day + city["required_days"] - 1
    schedule.append({
        "day_range": f"{start_day}-{end_day}",
        "place": city["place"]
    })
    # For next city, the flight day (current end_day) is overlapped.
    current_day = end_day

# Check that the final end_day equals the total_trip_days
if schedule[-1]["day_range"].split("-")[1] != str(total_trip_days):
    # Recover the integer value of final day from schedule if needed
    final_end_day = int(schedule[-1]["day_range"].split("-")[1])
    if final_end_day != total_trip_days:
        raise ValueError("The computed schedule does not match the total trip days.")

# Output the itinerary as a JSON formatted dictionary containing only day_range and place.
# The final output will be a list of segments (ordered itinerary).
print(json.dumps(schedule, indent=2))