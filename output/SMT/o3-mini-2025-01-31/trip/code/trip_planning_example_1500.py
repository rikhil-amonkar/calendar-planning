from z3 import *

# We have 10 cities indexed as follows:
# 0: Zurich      – 2 days; event: attend a conference in Zurich during day 7 and day 8.
# 1: Bucharest   – 2 days.
# 2: Hamburg     – 5 days.
# 3: Barcelona   – 4 days.
# 4: Reykjavik   – 5 days; event: visit relatives in Reykjavik between day 9 and day 13.
# 5: Stuttgart   – 5 days.
# 6: Stockholm   – 2 days.
# 7: Tallinn     – 4 days.
# 8: Milan       – 5 days; event: meet your friends at Milan between day 3 and day 7.
# 9: London      – 3 days; event: from day 1 to day 3 attend an annual show in London.
city_names = ["Zurich", "Bucharest", "Hamburg", "Barcelona", "Reykjavik", 
              "Stuttgart", "Stockholm", "Tallinn", "Milan", "London"]
req = [2, 2, 5, 4, 5, 5, 2, 4, 5, 3]

# Total required day credits is:
#   2 + 2 + 5 + 4 + 5 + 5 + 2 + 4 + 5 + 3 = 33.
#
# The rule is: if you do not fly on a day, you "get" 1 credit for that city,
# but if you fly on a day from city A to city B, then that day counts as 1 credit
# for A and also 1 credit for B. Hence the total day credits accumulated over
# T days (the base days) and F flight-days is equal to T + F.
# We are given T = 28 total days, so we must have:
#      28 + F = 33  ==>  F = 5 flights.
#
# IMPORTANT: Unlike some earlier puzzles where each city was visited exactly once
# (yielding many segments), here the sum of required credits is less than 28+9.
# Therefore, we allow that the visits to these cities may be “fragmented” over the 28-day itinerary.
# We do, however, require that each of the 10 cities is visited (at least once) and the total credits
# for each city equal its requirement.

DAYS = 28
REQUIRED_FLIGHTS = 5  # such that 28 + 5 = 33 total credits

# Allowed direct flights. Each pair is given as (from, to).
# (Remember to include both directions if the flight is bidirectional.)
allowed_flights = [
    # London and Hamburg
    (9, 2), (2, 9),
    # London and Reykjavik
    (9, 4), (4, 9),
    # Milan and Barcelona
    (8, 3), (3, 8),
    # Reykjavik and Barcelona
    (4, 3), (3, 4),
    # from Reykjavik to Stuttgart (unidirectional)
    (4, 5),
    # Stockholm and Reykjavik
    (6, 4), (4, 6),
    # London and Stuttgart
    (9, 5), (5, 9),
    # Milan and Zurich
    (8, 0), (0, 8),
    # London and Barcelona
    (9, 3), (3, 9),
    # Stockholm and Hamburg
    (6, 2), (2, 6),
    # Zurich and Barcelona
    (0, 3), (3, 0),
    # Stockholm and Stuttgart
    (6, 5), (5, 6),
    # Milan and Hamburg
    (8, 2), (2, 8),
    # Stockholm and Tallinn
    (6, 7), (7, 6),
    # Hamburg and Bucharest
    (2, 1), (1, 2),
    # London and Bucharest
    (9, 1), (1, 9),
    # Milan and Stockholm
    (8, 6), (6, 8),
    # Stuttgart and Hamburg
    (5, 2), (2, 5),
    # London and Zurich
    (9, 0), (0, 9),
    # Milan and Reykjavik
    (8, 4), (4, 8),
    # London and Stockholm
    (9, 6), (6, 9),
    # Milan and Stuttgart
    (8, 5), (5, 8),
    # Stockholm and Barcelona
    (6, 3), (3, 6),
    # London and Milan
    (9, 8), (8, 9),
    # Zurich and Hamburg
    (0, 2), (2, 0),
    # Bucharest and Barcelona
    (1, 3), (3, 1),
    # Zurich and Stockholm
    (0, 6), (6, 0),
    # Barcelona and Tallinn
    (3, 7), (7, 3),
    # Zurich and Tallinn
    (0, 7), (7, 0),
    # Hamburg and Barcelona
    (2, 3), (3, 2),
    # Stuttgart and Barcelona
    (5, 3), (3, 5),
    # Zurich and Reykjavik
    (0, 4), (4, 0),
    # Zurich and Bucharest
    (0, 1), (1, 0)
]

# Create the Z3 solver instance.
s = Solver()

# Variables:
# c[d] represents the base city on day d (0-indexed). It is an integer between 0 and 9.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Bool that indicates whether a flight occurs on day d.
# (By convention, day 0 has no flight.)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: each c[d] must be in [0, 9].
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# Day 0: No flight.
s.add(flight[0] == False)

# For days 1..DAYS-1, a flight occurs exactly when the city changes.
for d in range(1, DAYS):
    s.add(flight[d] == (c[d] != c[d-1]))
    # When a flight occurs on day d, the transition from day d-1 to d has to be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce that the total number of flight-days is exactly REQUIRED_FLIGHTS.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function: inCityOnDay(d, target) returns a condition that is True
# if on day d the itinerary "includes" the city 'target'.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute the day credits for each city.
# - On day 0, add 1 credit to c[0].
# - For each day d>=1:
#     If no flight on day d: add 1 credit to c[d].
#     If a flight occurs on day d: add 1 credit for c[d-1] and 1 for c[d].
counts = [Int(f"count_{i}") for i in range(len(city_names))]
for city in range(len(city_names)):
    base = If(c[0] == city, 1, 0)
    daily = []
    for d in range(1, DAYS):
        daily.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == base + Sum(daily))
    # Enforce that each city's total day credits equals its requirement.
    s.add(counts[city] == req[city])
    
    # Also, ensure that each city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event Constraints:
# 1. Zurich conference: "During day 7 and day 8, you have to attend a conference in Zurich."
# We'll require that on day 7 and day 8 (i.e. indices 6 and 7) the itinerary includes Zurich (city 0).
s.add(inCityOnDay(6, 0))
s.add(inCityOnDay(7, 0))

# 2. Reykjavik relatives: "visit relatives in Reykjavik between day 9 and day 13."
# This means at least on one of the days 9 to 13 (indices 8 through 12) the itinerary includes Reykjavik (city 4).
s.add(Or([inCityOnDay(d, 4) for d in range(8, 13)]))

# 3. Milan friends: "meet your friends at Milan between day 3 and day 7."
# So on at least one day between day 3 and day 7 (indices 2 through 6) include Milan (city 8).
s.add(Or([inCityOnDay(d, 8) for d in range(2, 7)]))

# 4. London annual show: "From day 1 to day 3, there is an annual show you want to attend in London."
# So on at least one day among day 1 to day 3 (indices 0 through 2) include London (city 9).
s.add(Or([inCityOnDay(d, 9) for d in range(0, 3)]))

# Finally, try to solve the constraints.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_info = f"Day {d+1:2d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = m[c[d-1]].as_long()
            arr = city_idx
            day_info += f" (Flight: {city_names[dep]} -> {city_names[arr]})"
        print(day_info)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]:12s}: {m.evaluate(counts[i])}")
else:
    print("No solution found")