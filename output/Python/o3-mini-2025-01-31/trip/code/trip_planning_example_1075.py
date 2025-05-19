import json

# Input constraints

# Cities with required durations
durations = {
    "Stuttgart": 5,
    "Edinburgh": 4,
    "Prague": 4,
    "Reykjavik": 5,
    "Vienna": 4,
    "Manchester": 2,
    "Split": 5,
    "Lyon": 3
}

# Flight connections (assuming bidirectional connectivity)
# Represented as a set of frozensets of two cities (each flight is undirected)
flights = {
    frozenset(["Reykjavik", "Stuttgart"]),
    frozenset(["Stuttgart", "Split"]),
    frozenset(["Stuttgart", "Vienna"]),
    frozenset(["Prague", "Manchester"]),
    frozenset(["Edinburgh", "Prague"]),
    frozenset(["Manchester", "Split"]),
    frozenset(["Prague", "Vienna"]),
    frozenset(["Vienna", "Manchester"]),
    frozenset(["Prague", "Split"]),
    frozenset(["Vienna", "Lyon"]),
    frozenset(["Stuttgart", "Edinburgh"]),
    frozenset(["Split", "Lyon"]),
    frozenset(["Stuttgart", "Manchester"]),
    frozenset(["Prague", "Lyon"]),
    frozenset(["Reykjavik", "Vienna"]),
    frozenset(["Prague", "Reykjavik"]),
    frozenset(["Vienna", "Split"])
}

# Special scheduling constraints:
# 1. Edinburgh must be occupied on days 5-8 (it has exactly 4 days)
# 2. Wedding in Split: must occur between day 19 and day 23 (Split has 5 days)

# We need an itinerary that visits all 8 cities. Note that the sum of durations is:
# 5 + 4 + 4 + 5 + 4 + 2 + 5 + 3 = 32 days.
# However, when flying, the flight day is counted in both cities.
# For a chain of 8 cities, there are 7 flight days (overlap days), so the effective total is 32 - 7 = 25 days.

# We choose an order that satisfies both the connectivity and the scheduling constraints.
# After testing various orders, one valid itinerary order is:
# 1. Stuttgart (5 days)
# 2. Edinburgh (4 days)          [Flight: Stuttgart -> Edinburgh]
# 3. Prague (4 days)             [Flight: Edinburgh -> Prague]
# 4. Reykjavik (5 days)          [Flight: Prague -> Reykjavik]
# 5. Vienna (4 days)             [Flight: Reykjavik -> Vienna]
# 6. Manchester (2 days)         [Flight: Vienna -> Manchester]
# 7. Split (5 days)              [Flight: Manchester -> Split]  (Wedding between day 19 and 23)
# 8. Lyon (3 days)               [Flight: Split -> Lyon]
#
# Verify flight connectivity for adjacent cities:
# Stuttgart -> Edinburgh : exists ("Stuttgart" and "Edinburgh")
# Edinburgh -> Prague   : exists ("Edinburgh" and "Prague")
# Prague -> Reykjavik   : exists ("Prague" and "Reykjavik")
# Reykjavik -> Vienna   : exists ("Reykjavik" and "Vienna")
# Vienna -> Manchester  : exists ("Vienna" and "Manchester")
# Manchester -> Split   : exists ("Manchester" and "Split")
# Split -> Lyon         : exists ("Split" and "Lyon")
#
# Now, we assign day ranges. The idea is that for the first city, the stay covers days [start, start + duration - 1].
# When flying from city A to B, the flight occurs on the last day of A and simultaneously the first day of B.
# So for each subsequent city, the start day is the same as the previous city’s end day.
#
# Let’s compute the itinerary day ranges:

itinerary_order = [
    "Stuttgart",  # 5 days
    "Edinburgh",  # 4 days; must cover days 5-8 (fulfilled if Stuttgart ends on day 5)
    "Prague",     # 4 days
    "Reykjavik",  # 5 days
    "Vienna",     # 4 days
    "Manchester", # 2 days
    "Split",      # 5 days; wedding between day 19 and 23 ensured by proper scheduling
    "Lyon"        # 3 days
]

# Calculate day ranges.
schedule = []
current_start = 1

# For each city, compute the day range.
# The flight day logic: for the first city, the range is [current_start, current_start+duration-1].
# For subsequent cities, they start on the previous city's end day because that day is shared.
for city in itinerary_order:
    d = durations[city]
    current_end = current_start + d - 1
    # Append the block information as a dict.
    schedule.append({
        "day_range": f"{current_start}-{current_end}",
        "place": city
    })
    # For next city, the start is the current end day (the flight day is shared)
    current_start = current_end

# At the end, current_end should be 25, based on the effective calculation:
# Total effective days = sum(durations) - (number of flights) = 32 - 7 = 25.
# We can assert that:
assert schedule[-1]["day_range"].split("-")[1] == "25", "The itinerary does not sum to 25 days."

# Output the result in JSON format.
print(json.dumps(schedule, indent=2))