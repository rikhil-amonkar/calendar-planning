from z3 import *

# City indices:
# 0: Reykjavik   – required 2 days; event: meet a friend in Reykjavik between day 3 and day 4.
# 1: Stockholm   – required 2 days; event: meet your friends in Stockholm between day 4 and day 5.
# 2: Porto       – required 5 days; event: attend a wedding in Porto between day 13 and day 17.
# 3: Nice        – required 3 days.
# 4: Venice      – required 4 days.
# 5: Vienna      – required 3 days; event: attend a workshop in Vienna between day 11 and day 13.
# 6: Split       – required 3 days.
# 7: Copenhagen  – required 2 days.
city_names = ["Reykjavik", "Stockholm", "Porto", "Nice", "Venice", "Vienna", "Split", "Copenhagen"]
required_credits = [2, 2, 5, 3, 4, 3, 3, 2]
# Total required credits = 2+2+5+3+4+3+3+2 = 24

# Total itinerary days:
DAYS = 17
# Credit counting rule:
#   - A non-flight day gives 1 credit for that day’s city.
#   - A day with a flight (i.e. when the city changes) gives 1 credit for the departure and 1 for the arrival.
# So total credits = DAYS + (# flight-days). We require 24 credits,
# thus (# flight-days) must be 24 - 17 = 7.
REQUIRED_FLIGHTS = 7

# Allowed direct flights (bidirectional):
# Using our city indices:
# • Copenhagen and Vienna           : (7,5) and (5,7)
# • Nice and Stockholm              : (3,1) and (1,3)
# • Split and Copenhagen            : (6,7) and (7,6)
# • Nice and Reykjavik              : (3,0) and (0,3)
# • Nice and Porto                  : (3,2) and (2,3)
# • Reykjavik and Vienna            : (0,5) and (5,0)
# • Stockholm and Copenhagen        : (1,7) and (7,1)
# • Nice and Venice                 : (3,4) and (4,3)
# • Nice and Vienna                 : (3,5) and (5,3)
# • Reykjavik and Copenhagen        : (0,7) and (7,0)
# • Nice and Copenhagen             : (3,7) and (7,3)
# • Stockholm and Vienna            : (1,5) and (5,1)
# • Venice and Vienna               : (4,5) and (5,4)
# • Copenhagen and Porto            : (7,2) and (2,7)
# • Reykjavik and Stockholm         : (0,1) and (1,0)
# • Stockholm and Split             : (1,6) and (6,1)
# • Split and Vienna                : (6,5) and (5,6)
# • Copenhagen and Venice           : (7,4) and (4,7)
# • Vienna and Porto                : (5,2) and (2,5)
allowed_flights = [
    (7,5), (5,7),
    (3,1), (1,3),
    (6,7), (7,6),
    (3,0), (0,3),
    (3,2), (2,3),
    (0,5), (5,0),
    (1,7), (7,1),
    (3,4), (4,3),
    (3,5), (5,3),
    (0,7), (7,0),
    (3,7), (7,3),
    (1,5), (5,1),
    (4,5), (5,4),
    (7,2), (2,7),
    (0,1), (1,0),
    (1,6), (6,1),
    (6,5), (5,6),
    (7,4), (4,7),
    (5,2), (2,5)
]

# Create the Z3 solver.
s = Solver()

# Variables:
# c[d] indicates the "base" city on day d (for days 0,...,DAYS-1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Bool that indicates if a flight happens on day d.
# By convention, day 0 has no flight.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: each day's city must be in {0,...,7}.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

s.add(flight[0] == False)  # No flight on day 0.

# For d=1..DAYS-1, determine if a flight is taken and check allowed transitions.
for d in range(1, DAYS):
    # A flight occurs on day d if the city changes from the previous day.
    s.add(flight[d] == (c[d] != c[d-1]))
    # If a flight occurs, then the transition must be in allowed_flights.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly REQUIRED_FLIGHTS flight-days.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper: inCityOnDay(d, target)
# Returns an expression that is true if on day d the itinerary "includes" target city.
# On a flight day, both the departure (from day d-1) and the arrival (c[d]) are counted.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits for each city.
# Credits come as follows:
# - Day 0: 1 credit for city c[0].
# - For each d>=1:
#     If no flight: add 1 credit for c[d].
#     If flight: add 1 credit for departure (c[d-1]) and 1 for arrival (c[d]).
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
    # Enforce that each city's computed credits equals its required number.
    s.add(counts[city] == required_credits[city])
    # Also ensure that each city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event Constraints:

# 1. Meet a friend in Reykjavik between day 3 and day 4.
# Days: day3 -> index 2, day4 -> index 3.
s.add(Or(inCityOnDay(2, 0), inCityOnDay(3, 0)))

# 2. Meet your friends in Stockholm between day 4 and day 5.
# Days: day4 -> index 3, day5 -> index 4.
s.add(Or(inCityOnDay(3, 1), inCityOnDay(4, 1)))

# 3. Attend a wedding in Porto between day 13 and day 17.
# Days: indices 12,13,14,15,16.
s.add(Or([inCityOnDay(d, 2) for d in range(12, 17)]))

# 4. Attend a workshop in Vienna between day 11 and day 13.
# Days: indices 10, 11, 12.
s.add(Or([inCityOnDay(d, 5) for d in range(10, 13)]))

# Solve the scheduling problem.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_str = f"Day {d+1:02d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = m[c[d-1]].as_long()
            arr = m[c[d]].as_long()
            day_str += f" (Flight: {city_names[dep]} -> {city_names[arr]})"
        print(day_str)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]:12s}: {m.evaluate(counts[i])}")
else:
    print("No solution found.")