from z3 import *

# City indices:
# 0: Seville     – required 5 days
# 1: Vilnius     – required 3 days
# 2: Santorini   – required 2 days
# 3: London      – required 2 days; event: meet friends in London between day 9 and day 10.
# 4: Stuttgart   – required 3 days; event: visit relatives in Stuttgart between day 7 and day 9.
# 5: Dublin      – required 3 days
# 6: Frankfurt   – required 5 days
city_names = ["Seville", "Vilnius", "Santorini", "London", "Stuttgart", "Dublin", "Frankfurt"]
required_credits = [5, 3, 2, 2, 3, 3, 5]
# Total required credits = 5 + 3 + 2 + 2 + 3 + 3 + 5 = 23

# Total itinerary days:
DAYS = 17
# Credit accounting: non-flight day gives 1 credit; a day with a flight (city change) gives 1 credit for departure and 1 for arrival.
# Total credits = DAYS + (# of flight days)
# We require 23 credits so (# of flight days) must be 23 - 17 = 6.
REQUIRED_FLIGHTS = 6

# Allowed direct flights. We'll use the indices above.
# Based on the problem statement:
# - Frankfurt and Dublin: (6,5) and (5,6)
# - Frankfurt and London: (6,3) and (3,6)
# - London and Dublin: (3,5) and (5,3)
# - Vilnius and Frankfurt: (1,6) and (6,1)
# - Frankfurt and Stuttgart: (6,4) and (4,6)
# - Dublin and Seville: (5,0) and (0,5)
# - London and Santorini: (3,2) and (2,3)
# - Stuttgart and London: (4,3) and (3,4)
# - Santorini and Dublin: (2,5) and (5,2)
allowed_flights = [
    (6,5), (5,6),
    (6,3), (3,6),
    (3,5), (5,3),
    (1,6), (6,1),
    (6,4), (4,6),
    (5,0), (0,5),
    (3,2), (2,3),
    (4,3), (3,4),
    (2,5), (5,2)
]

# Create a Z3 solver instance.
s = Solver()

# Variables:
# c[d] represents the "base" city on day d (0-indexed from 0 to DAYS-1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Bool that indicates if a flight occurs on day d.
# By convention, day 0 has no flight.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain for each day's city.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# Enforce no flight on day 0.
s.add(flight[0] == False)

# For days 1..DAYS-1, set flight indicators and allowed transitions.
for d in range(1, DAYS):
    # A flight occurs on day d if the city changes relative to previous day.
    s.add(flight[d] == (c[d] != c[d-1]))
    # If a flight occurs on day d, then the flight from c[d-1] to c[d] must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly REQUIRED_FLIGHTS flight-days.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function: inCityOnDay(d, target)
# Returns a condition which is True if on day d the itinerary "includes" the target city.
# On a flight day, both the departure (c[d-1]) and arrival (c[d]) are counted.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits for each city.
# Day 0 provides 1 credit to c[0]. For each subsequent day:
#  - If no flight: add 1 credit to the day's city.
#  - If flight: add 1 credit for departure and 1 for arrival.
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
    # Enforce that the computed credits equals the required number.
    s.add(counts[city] == required_credits[city])
    # Also ensure that each city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event Constraints:

# 1. Meet friends in London between day 9 and day 10.
#    (Days are numbered 1..17, so day 9 -> index 8 and day 10 -> index 9)
s.add(Or(inCityOnDay(8, 3), inCityOnDay(9, 3)))

# 2. Visit relatives in Stuttgart between day 7 and day 9.
#    (Day 7 -> index 6, day 8 -> index 7, day 9 -> index 8)
s.add(Or([inCityOnDay(d, 4) for d in [6,7,8]]))

# Solve the model.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_output = f"Day {d+1:02d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = m[c[d-1]].as_long()
            arr = m[c[d]].as_long()
            day_output += f" (Flight: {city_names[dep]} -> {city_names[arr]})"
        print(day_output)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]:12s}: {m.evaluate(counts[i])}")
else:
    print("No solution found.")