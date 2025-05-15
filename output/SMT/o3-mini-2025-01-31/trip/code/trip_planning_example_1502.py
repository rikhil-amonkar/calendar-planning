from z3 import *

# City indices and names:
# 0: Santorini   (3 days)
# 1: Valencia    (4 days)
# 2: Madrid      (2 days; event: annual show in Madrid from day 6 to day 7)
# 3: Seville     (2 days)
# 4: Bucharest   (3 days)
# 5: Vienna      (4 days; event: wedding in Vienna between day 3 and day 6)
# 6: Riga        (4 days; event: conference in Riga on day 20 or day 23)
# 7: Tallinn     (5 days; event: workshop in Tallinn between day 23 and day 27)
# 8: Krakow      (5 days; event: meet friends in Krakow between day 11 and day 15)
# 9: Frankfurt   (4 days)
city_names = ["Santorini", "Valencia", "Madrid", "Seville", "Bucharest",
              "Vienna", "Riga", "Tallinn", "Krakow", "Frankfurt"]

# Required day contributions for each city.
req = [3, 4, 2, 2, 3, 4, 4, 5, 5, 4]
# Total required contributions = 3+4+2+2+3+4+4+5+5+4 = 36.
# There are 27 base days.
# Since a flight day (when a flight occurs) counts for both the departure and arrival cities,
# total contributions = 27 + (#flights). To reach 36, we require 27 + (#flights) = 36, hence #flights = 9.
# This splits the itinerary into 10 segments (each segment representing one visited city).

# Allowed direct flights (each flight is bidirectional unless stated otherwise):
allowed_flights = [
    # Vienna and Bucharest
    (5,4), (4,5),
    # Santorini and Madrid
    (0,2), (2,0),
    # Seville and Valencia
    (3,1), (1,3),
    # Vienna and Seville
    (5,3), (3,5),
    # Madrid and Valencia
    (2,1), (1,2),
    # Bucharest and Riga
    (4,6), (6,4),
    # Valencia and Bucharest
    (1,4), (4,1),
    # Santorini and Bucharest
    (0,4), (4,0),
    # Vienna and Valencia
    (5,1), (1,5),
    # Vienna and Madrid
    (5,2), (2,5),
    # Valencia and Krakow
    (1,8), (8,1),
    # Valencia and Frankfurt
    (1,9), (9,1),
    # Krakow and Frankfurt
    (8,9), (9,8),
    # from Riga to Tallinn (one-way)
    (6,7),
    # Vienna and Krakow
    (5,8), (8,5),
    # Vienna and Frankfurt
    (5,9), (9,5),
    # Madrid and Seville
    (2,3), (3,2),
    # Santorini and Vienna
    (0,5), (5,0),
    # Vienna and Riga
    (5,6), (6,5),
    # Frankfurt and Tallinn
    (9,7), (7,9),
    # Frankfurt and Bucharest
    (9,4), (4,9),
    # Madrid and Bucharest
    (2,4), (4,2),
    # Frankfurt and Riga
    (9,6), (6,9),
    # Madrid and Frankfurt
    (2,9), (9,2)
]

# Total base days in the itinerary.
DAYS = 27

# Create Z3 variables:
# c[d] represents the base city on day d (0-indexed, so day d corresponds to day d+1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean variable indicating whether a flight occurs on day d (d>=1).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] indicates that day d is the start of a segment (day 0 always, and any day where a flight occurs).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Each base day must be assigned a valid city (0 through 9).
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < 10)

# Day 0 is always the start of a segment.
s.add(isSeg[0] == True)

# For days 1 .. DAYS-1, define flight indicator and segment flag.
for d in range(1, DAYS):
    # A flight occurs on day d if the city changes from day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs on day d, ensure the flight route is allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Exactly 9 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 9)

# The starting city of each segment (day 0 and any day with a flight) must be distinct.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally, enforce that every city is visited at least once.
for city in range(10):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Compute day contributions for each city.
# Day 0 contributes 1 for c[0]. 
# For each day d from 1 to DAYS-1:
#  If a flight occurs on day d, add 1 for the departure city (c[d-1]) and 1 for the arrival (c[d]);
#  Else add 1 for c[d] only.
counts = [Int(f"count_{i}") for i in range(10)]
for i in range(10):
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
# This returns a constraint indicating that on day d, the itinerary "includes" the target city.
# If a flight occurs on day d, then the day counts for both the departure and arrival cities.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Event constraints:

# 1. Annual show in Madrid (city 2) from day 6 to day 7.
# Days 6 and 7 correspond to indices 5 and 6.
madrid_show = [inCityOnDay(d, 2) for d in [5, 6]]
s.add(Or(madrid_show))

# 2. Wedding in Vienna (city 5) between day 3 and day 6.
# That corresponds to days 3,4,5,6 (indices 2,3,4,5).
wedding_vienna = [inCityOnDay(d, 5) for d in range(2, 6)]
s.add(Or(wedding_vienna))

# 3. Conference in Riga (city 6) during day 20 and day 23.
# That is, on at least one of day 20 (index 19) or day 23 (index 22) the traveler is in Riga.
conference_riga = [inCityOnDay(d, 6) for d in [19, 22]]
s.add(Or(conference_riga))

# 4. Workshop in Tallinn (city 7) between day 23 and day 27.
# That covers days 23,24,25,26,27 which are indices 22,23,24,25,26.
workshop_tallinn = [inCityOnDay(d, 7) for d in range(22, 27)]
s.add(Or(workshop_tallinn))

# 5. Meet friends in Krakow (city 8) between day 11 and day 15.
# That corresponds to days 11,12,13,14,15 which are indices 10,11,12,13,14.
friends_krakow = [inCityOnDay(d, 8) for d in range(10, 15)]
s.add(Or(friends_krakow))

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
    for i in range(10):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")