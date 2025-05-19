import json

# Input parameters (constraints and flight connections are encoded in the following variables)

# Total days in trip and required durations in each city (as allocated days)
total_days = 17
cities = ["Brussels", "Lisbon", "Venice", "London", "Reykjavik", "Madrid", "Santorini"]
# Allocated durations for each city that, when overlapped on transition days, sum to total_days:
# Formula: total = sum(duration) - (number_of_transitions) and we have 7 cities so 6 transitions.
# Given constraints:
#   Brussels (conference on days 1-2)        -> 2 days
#   Lisbon                                   -> 4 days
#   Venice (3 days; relatives visit between day5 and day7) -> 3 days
#   London                                   -> 3 days
#   Reykjavik                                -> 3 days
#   Madrid (5 days; wedding between day7 and day11, Madrid gets day11) -> 5 days
#   Santorini                                -> 3 days
durations = {
    "Brussels": 2,
    "Lisbon": 4,
    "Venice": 3,
    "London": 3,
    "Reykjavik": 3,
    "Madrid": 5,
    "Santorini": 3
}

# Flight connections (each edge means a direct flight between the two cities)
# Note: We assume flights to be bidirectional.
flights = {
    "Venice": ["Madrid", "Brussels", "Santorini", "London", "Lisbon"],
    "Madrid": ["Venice", "London", "Santorini", "Lisbon", "Reykjavik", "Brussels"],
    "Lisbon": ["Reykjavik", "Venice", "London", "Brussels", "Madrid"],
    "Brussels": ["Venice", "London", "Lisbon", "Reykjavik", "Madrid"],
    "London": ["Brussels", "Madrid", "Santorini", "Reykjavik", "Lisbon", "Venice"],
    "Reykjavik": ["Lisbon", "Madrid", "London", "Brussels"],
    "Santorini": ["Venice", "London", "Madrid"]
}

# Defined constraints:
#  - Brussels must be visited on days 1 and 2 (conference)
#  - Venice: 3 days, with relative visit required between day 5 and day 7 (so at least one day of Venice falls in that range)
#  - London must be 3 days.
#  - Lisbon must be 4 days.
#  - Reykjavik must be 3 days.
#  - Santorini must be 3 days.
#  - Madrid: 5 days with wedding between day 7 and day 11 (inclusive).
#
# We now choose an itinerary order (sequence of cities) such that:
#   1. The trip totals 17 days using overlapping flight days.
#   2. Each flight between consecutive cities is a direct flight based on the provided flight connections.
#   3. The Venice and Madrid timing constraints are respected.
#
# One valid itinerary order that meets these constraints is:
#   1. Brussels      (days 1-2)              [conference: days 1-2]
#   2. Lisbon        (days 2-5)              [4 days]
#   3. Venice        (days 5-7)              [3 days; relatives visit fall on day 5-7]
#   4. London        (days 7-9)              [3 days]
#   5. Reykjavik     (days 9-11)             [3 days]
#   6. Madrid        (days 11-15)            [5 days; wedding can take place on day 11]
#   7. Santorini     (days 15-17)            [3 days]
#
# Verification of direct flights:
#   Brussels -> Lisbon is available.
#   Lisbon -> Venice is available.
#   Venice -> London is available.
#   London -> Reykjavik is available.
#   Reykjavik -> Madrid is available.
#   Madrid -> Santorini is available.

itinerary_order = ["Brussels", "Lisbon", "Venice", "London", "Reykjavik", "Madrid", "Santorini"]

# Compute day ranges based on overlapping flight rules:
# The first city starts on day 1 and occupies its full duration.
# For subsequent cities, the starting day is the same as the previous city's end day.
schedule = []
current_day = 1

for i, city in enumerate(itinerary_order):
    dur = durations[city]
    # For the first city, assign full duration. For subsequent, the flight day (current_day) is shared.
    start_day = current_day
    end_day = start_day + dur - 1  # because the first day of stay is shared as arrival day
    schedule.append({"day_range": f"{start_day}-{end_day}", "place": city})
    # Next city's start day is the same as this end day (overlap)
    current_day = end_day

# The computed itinerary should finish on day 17 if the math works out.
if current_day != total_days:
    raise ValueError("The computed itinerary does not match the total trip days. Check constraints and durations.")

# Output the schedule as a JSON-formatted dictionary (list of day_range and place)
print(json.dumps(schedule, indent=2))