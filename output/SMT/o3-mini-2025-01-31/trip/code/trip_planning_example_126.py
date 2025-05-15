from z3 import *

# City indices and names:
# 0: Seville    (6 days)
# 1: Paris      (2 days)
# 2: Krakow     (5 days; event: workshop in Krakow between day 1 and day 5)
city_names = ["Seville", "Paris", "Krakow"]

# Required day counts per city.
req = [6, 2, 5]
# Total required contributions = 6 + 2 + 5 = 13.
# We have 11 base days.
# Each flight day counts for both the departure and arrival cities.
# Hence total contributions = 11 + (#flights).
# To reach 13, we need 2 flights.
#
# With 2 flights the itinerary is segmented into 3 segments.
# We enforce that the starting city of each segment is unique,
# so every city is visited exactly once.

# Allowed direct flights.
# Given flights: "Krakow and Paris" and "Paris and Seville"
# Assuming direct flights are bidirectional,
# our allowed flight pairs are:
allowed_flights = [
    (2, 1), (1, 2),  # Krakow <-> Paris
    (1, 0), (0, 1)   # Paris <-> Seville
]

# Total base days.
DAYS = 11

# Create Z3 variables:
# c[d] is the base city on day d (0-indexed: day d+1)
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean variable indicating whether a flight happens on day d (d>=1)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] indicates if day d is the start of a new segment (always True for day 0, and on flight days).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Each base day must be assigned a city from 0 to 2.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < 3)

# Day 0 is always a segment start.
s.add(isSeg[0] == True)

# For days 1 to DAYS-1, define flight indicator and segment flag.
for d in range(1, DAYS):
    # A flight occurs on day d if the base city changes from the previous day.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If there is a flight on day d, then the flight route must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Exactly 2 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 2)

# The starting city of each segment (day 0 and any day with a flight) must be distinct.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally, enforce that every city is visited.
for city in range(3):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Compute day contributions for each city.
# Day 0 contributes 1 for c[0].
# For each day d from 1 to DAYS-1:
#  - if a flight occurs on day d, then day d adds 1 for both the departure (c[d-1])
#    and the arrival (c[d]),
#  - else it adds 1 for c[d] only.
counts = [Int(f"count_{i}") for i in range(3)]
for i in range(3):
    init = If(c[0] == i, 1, 0)
    daily = []
    for d in range(1, DAYS):
        daily.append(
            If(flight[d],
               If(c[d-1] == i, 1, 0) + If(c[d] == i, 1, 0),
               If(c[d] == i, 1, 0)
            )
        )
    s.add(counts[i] == init + Sum(daily))
    s.add(counts[i] == req[i])

# Helper function: inCityOnDay(d, target)
# Represents that on day d, the itinerary "includes" the target city.
# If a flight occurs on day d, then both the departure (day d-1) and arrival (d) count.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Event constraint:
# Attend a workshop in Krakow (city 2) between day 1 and day 5.
# That means at least one day among day 1 to day 5 (indices 0 to 4) must include Krakow.
# (Since day numbering here: day 1 is index 0, day 2 is index 1, etc.)
workshop_krakow = [inCityOnDay(d, 2) for d in range(0, 5)]
s.add(Or(workshop_krakow))

# Check for a solution.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        base = m[c[d]].as_long()
        day_info = f"Day {d+1:2d}: In {city_names[base]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[base]
            day_info += f" (Flight: {dep} -> {arr})"
        print(day_info)
    print("\nCity day counts:")
    for i in range(3):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")