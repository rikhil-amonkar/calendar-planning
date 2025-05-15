from z3 import *

# City indices and names:
# 0: Krakow     (5 days)
# 1: Frankfurt   (4 days)
# 2: Oslo        (3 days; event: visit relatives in Oslo between day 16 and day 18)
# 3: Dubrovnik   (5 days; event: meet friends at Dubrovnik between day 5 and day 9)
# 4: Naples      (5 days)
city_names = ["Krakow", "Frankfurt", "Oslo", "Dubrovnik", "Naples"]

# Required day counts per city.
req = [5, 4, 3, 5, 5]
# Total required day contributions = 5+4+3+5+5 = 22.
# We have 18 base days.
# Each flight day (when traveling from A to B) counts for both cities A and B.
# Thus total contributions = base days + number of flights.
# To satisfy 18 + f = 22, we require f = 4 flights.
# That means that the itinerary is segmented into 5 segments, each corresponding to one city.
# In our model we will enforce that the starting city of each segment is distinct.

# Allowed direct flights (bidirectional):
allowed_flights = [
    # Dubrovnik and Oslo
    (3, 2), (2, 3),
    # Frankfurt and Krakow
    (1, 0), (0, 1),
    # Frankfurt and Oslo
    (1, 2), (2, 1),
    # Dubrovnik and Frankfurt
    (3, 1), (1, 3),
    # Krakow and Oslo
    (0, 2), (2, 0),
    # Naples and Oslo
    (4, 2), (2, 4),
    # Naples and Dubrovnik
    (4, 3), (3, 4),
    # Naples and Frankfurt
    (4, 1), (1, 4)
]

# Total itinerary base days:
DAYS = 18

# Create Z3 variables:
# c[d]: base city on day d (0-indexed, representing day d+1)
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d]: Bool variable indicating if a flight occurs on day d (for d>=1)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d]: Bool variable that flags day d as the start of a segment (day 0 always, and those with a flight)
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Each day's base city must be one of the five cities.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < 5)

# Day 0 is always a segment start.
s.add(isSeg[0] == True)

# For days 1 to DAYS-1, define flight indicator and segment flag.
for d in range(1, DAYS):
    # A flight occurs on day d if the base city changes from day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If there is a flight on day d then the flight route must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Exactly 4 flights occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 4)

# The starting city of each segment (day 0 and any day with a flight) must be distinct.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally ensure that every city is visited at least once.
for city in range(5):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Compute day contributions for each city.
# On day 0, contribute 1 for c[0].
# For each day d from 1 to DAYS-1:
#   if a flight occurs on day d: add 1 for departure city (c[d-1]) and 1 for arrival city (c[d]);
#   otherwise add 1 for c[d].
counts = [Int(f"count_{i}") for i in range(5)]
for i in range(5):
    initial = If(c[0] == i, 1, 0)
    daily = []
    for d in range(1, DAYS):
        daily.append(
            If(flight[d],
               (If(c[d-1] == i, 1, 0) + If(c[d] == i, 1, 0)),
               If(c[d] == i, 1, 0)
            )
        )
    s.add(counts[i] == initial + Sum(daily))
    s.add(counts[i] == req[i])

# Helper function: inCityOnDay(d, target)
# If a flight occurs on day d, then that day is counted for both the departure (d-1) and arrival (d).
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Event constraints:

# 1. Meet friends at Dubrovnik (city 3) between day 5 and day 9.
# Days 5 to 9 correspond to indices 4, 5, 6, 7, 8.
dubrovnik_event = [inCityOnDay(d, 3) for d in range(4, 9)]
s.add(Or(dubrovnik_event))

# 2. Visit relatives in Oslo (city 2) between day 16 and day 18.
# Days 16 to 18 correspond to indices 15, 16, 17.
oslo_relatives = [inCityOnDay(d, 2) for d in range(15, 18)]
s.add(Or(oslo_relatives))

# Check for a solution.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        base = m[c[d]].as_long()
        day_str = f"Day {d+1:2d}: In {city_names[base]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[base]
            day_str += f" (Flight: {dep} -> {arr})"
        print(day_str)
    print("\nCity day counts:")
    for i in range(5):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")