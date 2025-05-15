from z3 import *

# City indices and names:
# 0: Berlin     (3 days; event: conference in Berlin on day 1 and day 3)
# 1: Nice       (5 days)
# 2: Athens     (5 days)
# 3: Stockholm  (5 days)
# 4: Barcelona  (2 days; event: workshop in Barcelona between day 3 and day 4)
# 5: Vilnius    (4 days)
# 6: Lyon       (2 days; event: wedding in Lyon between day 4 and day 5)
city_names = ["Berlin", "Nice", "Athens", "Stockholm", "Barcelona", "Vilnius", "Lyon"]

# Required day contributions for each city:
req = [3, 5, 5, 5, 2, 4, 2]
# Total required contributions = 3 + 5 + 5 + 5 + 2 + 4 + 2 = 26.
# We plan 20 base days. Since every flight day yields an extra contribution (departure and arrival),
# we have: base_days + (#flights) = total contributions, hence #flights = 26 - 20 = 6.
# This divides our itinerary into 7 segments (one segment per visited city).

# Allowed direct flights (bidirectional):
# Lyon and Nice
# Stockholm and Athens
# Nice and Athens
# Berlin and Athens
# Berlin and Nice
# Berlin and Barcelona
# Berlin and Vilnius
# Barcelona and Nice
# Athens and Vilnius
# Berlin and Stockholm
# Nice and Stockholm
# Barcelona and Athens
# Barcelona and Stockholm
# Barcelona and Lyon
allowed_flights = [
    (6, 1), (1, 6),
    (3, 2), (2, 3),
    (1, 2), (2, 1),
    (0, 2), (2, 0),
    (0, 1), (1, 0),
    (0, 4), (4, 0),
    (0, 5), (5, 0),
    (4, 1), (1, 4),
    (2, 5), (5, 2),
    (0, 3), (3, 0),
    (1, 3), (3, 1),
    (4, 2), (2, 4),
    (4, 3), (3, 4),
    (4, 6), (6, 4)
]

DAYS = 20  # base days

# Create Z3 variables:
# c[d] is the base city for day d (0-indexed: day d corresponds to day d+1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean that indicates a flight occurs on day d (for d>=1)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a segment (day0 always a segment start)
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Domain constraints: each base city must be in 0..6.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < 7)

# Day 0 is always the start of a new segment.
s.add(isSeg[0] == True)

# Define flight indicators and allowed transitions for days 1 to DAYS-1.
for d in range(1, DAYS):
    # A flight occurs on day d if the base city changes from day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs on day d, the flight route must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Exactly 6 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 6)

# Ensure that the starting city of each segment (day 0 and days with a flight) is distinct.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally, enforce that every city is visited at least once.
for city in range(7):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Compute day contributions for each city.
# Day 0 contributes 1 for the city it is in.
# For each day d from 1 to DAYS-1:
#   If a flight occurs on day d, then the day contributes 1 to both c[d-1] and c[d].
#   Otherwise, it contributes 1 only to c[d].
counts = [Int(f"count_{city}") for city in range(7)]
for city in range(7):
    init = If(c[0] == city, 1, 0)
    daily = []
    for d in range(1, DAYS):
        daily.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == init + Sum(daily))
    s.add(counts[city] == req[city])

# Helper function: inCityOnDay(d, target)
# Returns a constraint indicating that on day d, the itinerary "includes" the target city.
# If a flight occurs on day d, both the departure (c[d-1]) and arrival (c[d]) count.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Event constraints:

# 1. Conference in Berlin (city 0) must be attended on day 1 and day 3.
#    Day 1 corresponds to index 0 and day 3 to index 2.
s.add(inCityOnDay(0, 0))
s.add(inCityOnDay(2, 0))

# 2. Workshop in Barcelona (city 4) must be attended on at least one of day 3 or day 4.
#    Day 3 and day 4 correspond to indices 2 and 3.
workshop_barcelona = [inCityOnDay(d, 4) for d in [2, 3]]
s.add(Or(workshop_barcelona))

# 3. Wedding in Lyon (city 6) must be attended on at least one of day 4 or day 5.
#    Day 4 and day 5 correspond to indices 3 and 4.
wedding_lyon = [inCityOnDay(d, 6) for d in [3, 4]]
s.add(Or(wedding_lyon))

# Check for solution.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_index = m[c[d]].as_long()
        day_str = f"Day {d+1:2d}: {city_names[city_index]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[city_index]
            day_str += f" (Flight: {dep} -> {arr})"
        print(day_str)
    print("\nCity day counts:")
    for i in range(7):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")