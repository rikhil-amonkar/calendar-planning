from z3 import *

# City indices:
# 0: Mykonos    – required 4 days.
# 1: Nice       – required 3 days; event: attend a conference in Nice on day 14 and day 16.
# 2: London     – required 2 days.
# 3: Copenhagen – required 3 days.
# 4: Oslo       – required 5 days; event: meet a friend in Oslo between day 10 and day 14.
# 5: Tallinn    – required 4 days.
city_names = ["Mykonos", "Nice", "London", "Copenhagen", "Oslo", "Tallinn"]
required_credits = [4, 3, 2, 3, 5, 4]
# Total required credits = 4 + 3 + 2 + 3 + 5 + 4 = 21

# Total itinerary days:
DAYS = 16
# Credit rule:
# - A day with no flight gives 1 credit to that day’s city.
# - A day with a flight gives 1 credit for the departure and 1 for the arrival.
# Hence, total credits = DAYS + (# flight-days).
# We require 21 credits, so the number of flight-days must be 21 - 16 = 5.
REQUIRED_FLIGHTS = 5

# Allowed direct flights (bidirectional):
# London and Copenhagen        : (2, 3) and (3, 2)
# Copenhagen and Tallinn       : (3, 5) and (5, 3)
# Tallinn and Oslo             : (5, 4) and (4, 5)
# Mykonos and London           : (0, 2) and (2, 0)
# Oslo and Nice                : (4, 1) and (1, 4)
# London and Nice              : (2, 1) and (1, 2)
# Mykonos and Nice             : (0, 1) and (1, 0)
# London and Oslo              : (2, 4) and (4, 2)
# Copenhagen and Nice          : (3, 1) and (1, 3)
# Copenhagen and Oslo          : (3, 4) and (4, 3)
allowed_flights = [
    (2, 3), (3, 2),
    (3, 5), (5, 3),
    (5, 4), (4, 5),
    (0, 2), (2, 0),
    (4, 1), (1, 4),
    (2, 1), (1, 2),
    (0, 1), (1, 0),
    (2, 4), (4, 2),
    (3, 1), (1, 3),
    (3, 4), (4, 3)
]

s = Solver()

# Variables:
# c[d] represents the city on day d (for d=0,...,DAYS-1)
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] indicates if a flight is taken on day d.
# Convention: day 0 has no flight.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: each day's city is in {0,...,5}.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))
s.add(flight[0] == False)

# For days 1..DAYS-1, establish flight indicator and allowed flight constraints.
for d in range(1, DAYS):
    # A flight occurs on day d if the city on day d differs from day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    # If a flight happens, the transition must be an allowed flight.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly REQUIRED_FLIGHTS flight-days.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper: inCityOnDay(d, target)
# Returns an expression that is True if on day d the itinerary "includes" the target city.
# On a flight day, both the departure (c[d-1]) and arrival (c[d]) count.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits for each city.
# Day 0 gives 1 credit to c[0]. For d>=1, if no flight, add 1 credit for c[d],
# and if a flight occurs, add 1 credit for both the departure (c[d-1]) and arrival (c[d]).
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
    # Enforce the required credits for each city.
    s.add(counts[city] == required_credits[city])
    # Enforce that each city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event constraints:

# 1. Conference in Nice on day 14 and day 16.
# Day 14 is index 13 and day 16 is index 15; on these days the itinerary must include Nice (city 1).
s.add(inCityOnDay(13, 1))
s.add(inCityOnDay(15, 1))

# 2. Meet a friend in Oslo between day 10 and day 14.
# That means on at least one day in the interval day 10 to day 14 (indices 9 to 13),
# the itinerary must include Oslo (city 4).
s.add(Or([inCityOnDay(d, 4) for d in range(9, 14)]))

# Solve the scheduling problem.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_line = f"Day {d+1:02d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = m[c[d-1]].as_long()
            arr = m[c[d]].as_long()
            day_line += f" (Flight: {city_names[dep]} -> {city_names[arr]})"
        print(day_line)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]:10s}: {m.evaluate(counts[i])}")
else:
    print("No solution found.")