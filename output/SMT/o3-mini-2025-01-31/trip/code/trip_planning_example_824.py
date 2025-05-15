from z3 import *

# City indices and names:
# 0: Berlin      (5 days, event: annual show in Berlin from day 1 to day 5)
# 1: Split       (3 days)
# 2: Bucharest   (3 days, event: visit relatives in Bucharest between day 13 and day 15)
# 3: Riga        (5 days)
# 4: Lisbon      (3 days)
# 5: Tallinn     (4 days)
# 6: Lyon        (5 days, event: wedding in Lyon between day 7 and day 11)
city_names = ["Berlin", "Split", "Bucharest", "Riga", "Lisbon", "Tallinn", "Lyon"]

# Required day contributions for each city:
req = [5, 3, 3, 5, 3, 4, 5]
# Total required contributions = 5+3+3+5+3+4+5 = 28.
# Base days = 22.
# Each flight day (when a flight occurs) gives an extra contribution (counts for both departure and arrival).
# Therefore, we require exactly 22 + (#flights) = 28, which implies (#flights) = 6.
# This splits the itinerary into 7 segments, each corresponding to one visited city.

# Allowed direct flights:
# Lisbon and Bucharest => (4,2) and (2,4)
# Berlin and Lisbon    => (0,4) and (4,0)
# Bucharest and Riga   => (2,3) and (3,2)
# Berlin and Riga      => (0,3) and (3,0)
# Split and Lyon       => (1,6) and (6,1)
# Lisbon and Riga      => (4,3) and (3,4)
# from Riga to Tallinn => (3,5)    (one-way only)
# Berlin and Split     => (0,1) and (1,0)
# Lyon and Lisbon      => (6,4) and (4,6)
# Berlin and Tallinn   => (0,5) and (5,0)
# Lyon and Bucharest   => (6,2) and (2,6)
allowed_flights = [
    (4, 2), (2, 4),
    (0, 4), (4, 0),
    (2, 3), (3, 2),
    (0, 3), (3, 0),
    (1, 6), (6, 1),
    (4, 3), (3, 4),
    (3, 5),   # from Riga to Tallinn only
    (0, 1), (1, 0),
    (6, 4), (4, 6),
    (0, 5), (5, 0),
    (6, 2), (2, 6)
]

# Total base days in the itinerary:
DAYS = 22

# Create Z3 variables:
# c[d] represents the base city on day d (0-indexed, representing day d+1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean variable indicating whether a flight occurs on day d (for d >= 1).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is true if day d is the start of a new segment (day 0 always, and any day where a flight occurs).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Each day's base city must be valid:
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < 7)

# Day 0 is always the start of a segment.
s.add(isSeg[0] == True)

# For each day d from 1 to DAYS-1, define flight indicator and segment flag.
for d in range(1, DAYS):
    # A flight occurs on day d if the base city changes from the previous day.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs on day d, then (c[d-1], c[d]) must be an allowed flight.
    s.add(Implies(flight[d], 
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Exactly 6 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 6)

# The starting city of each segment (day 0 and any d where flight[d] is true) must be distinct.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally, enforce that every city is visited at least once.
for city in range(7):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Compute day contributions for each city.
# On day 0, we add 1 for the city c[0].
# For each subsequent day d in 1..DAYS-1:
#   If a flight occurs on day d, add 1 for both the departure (c[d-1]) and arrival (c[d]).
#   Otherwise, add 1 for the city c[d].
counts = [Int(f"count_{i}") for i in range(7)]
for i in range(7):
    init = If(c[0] == i, 1, 0)
    daily_contrib = []
    for d in range(1, DAYS):
        daily_contrib.append(
            If(flight[d],
               If(c[d-1] == i, 1, 0) + If(c[d] == i, 1, 0),
               If(c[d] == i, 1, 0)
            )
        )
    s.add(counts[i] == init + Sum(daily_contrib))
    s.add(counts[i] == req[i])

# Helper function: inCityOnDay(d, target)
# This returns a condition that day d "includes" the target city.
# If a flight occurs on day d, then both the departure city (c[d-1]) and the arrival city (c[d]) count.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Event constraints:
# 1. Annual show in Berlin (city 0) from day 1 to day 5 (indices 0-4).
berlin_show = [inCityOnDay(d, 0) for d in range(0, 5)]
s.add(Or(berlin_show))

# 2. Visit relatives in Bucharest (city 2) between day 13 and day 15 (indices 12,13,14).
bucharest_event = [inCityOnDay(d, 2) for d in range(12, 15)]
s.add(Or(bucharest_event))

# 3. Wedding in Lyon (city 6) between day 7 and day 11 (indices 6 to 10).
wedding_lyon = [inCityOnDay(d, 6) for d in range(6, 11)]
s.add(Or(wedding_lyon))

# Check for a solution.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        base_city = m[c[d]].as_long()
        day_str = f"Day {d+1:2d}: {city_names[base_city]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[base_city]
            day_str += f" (Flight: {dep} -> {arr})"
        print(day_str)
    print("\nCity day counts:")
    for i in range(7):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")