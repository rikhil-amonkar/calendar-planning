from z3 import *

# City indices and required day credits:
# 0: Prague      – required 5 days.
# 1: Tallinn     – required 3 days; event: visit relatives between day 18 and day 20.
# 2: Warsaw      – required 2 days.
# 3: Porto       – required 3 days.
# 4: Naples      – required 5 days.
# 5: Milan       – required 3 days; event: meet friend between day 24 and day 26.
# 6: Lisbon      – required 5 days.
# 7: Santorini   – required 5 days.
# 8: Riga        – required 4 days; event: annual show from day 5 to day 8.
# 9: Stockholm   – required 2 days.

city_names = ["Prague", "Tallinn", "Warsaw", "Porto", "Naples", "Milan", "Lisbon", "Santorini", "Riga", "Stockholm"]
required_credits = [5, 3, 2, 3, 5, 3, 5, 5, 4, 2]

# Total required credits = 5+3+2+3+5+3+5+5+4+2 = 37

# Total itinerary days:
DAYS = 28
# Flight rule:
#   On a day without a flight: 1 credit is given for that day's city.
#   On a flight day: you get 1 credit for the departure city and 1 for the arrival city.
# So total credits = DAYS + (# flight-days)
# We require 37 credits => (# flight-days) = 37 - 28 = 9.
REQUIRED_FLIGHTS = 9

# Allowed direct flights (some bidirectional, some unidirectional):
# Using indices from above.
allowed_flights = [
    # Riga and Prague: bidirectional
    (8, 0), (0, 8),
    # Stockholm and Milan:
    (9, 5), (5, 9),
    # Riga and Milan:
    (8, 5), (5, 8),
    # Lisbon and Stockholm:
    (6, 9), (9, 6),
    # From Stockholm to Santorini (unidirectional):
    (9, 7),
    # Naples and Warsaw:
    (4, 2), (2, 4),
    # Lisbon and Warsaw:
    (6, 2), (2, 6),
    # Naples and Milan:
    (4, 5), (5, 4),
    # Lisbon and Naples:
    (6, 4), (4, 6),
    # From Riga to Tallinn (unidirectional):
    (8, 1),
    # Tallinn and Prague:
    (1, 0), (0, 1),
    # Stockholm and Warsaw:
    (9, 2), (2, 9),
    # Riga and Warsaw:
    (8, 2), (2, 8),
    # Lisbon and Riga:
    (6, 8), (8, 6),
    # Riga and Stockholm:
    (8, 9), (9, 8),
    # Lisbon and Porto:
    (6, 3), (3, 6),
    # Lisbon and Prague:
    (6, 0), (0, 6),
    # Milan and Porto:
    (5, 3), (3, 5),
    # Prague and Milan:
    (0, 5), (5, 0),
    # Lisbon and Milan:
    (6, 5), (5, 6),
    # Warsaw and Porto:
    (2, 3), (3, 2),
    # Warsaw and Tallinn:
    (2, 1), (1, 2),
    # Santorini and Milan:
    (7, 5), (5, 7),
    # Stockholm and Prague:
    (9, 0), (0, 9),
    # Stockholm and Tallinn:
    (9, 1), (1, 9),
    # Warsaw and Milan:
    (2, 5), (5, 2),
    # Santorini and Naples:
    (7, 4), (4, 7),
    # Warsaw and Prague:
    (2, 0), (0, 2)
]

# Create the Z3 solver.
s = Solver()

# Variables:
# c[d] = city (0..9) on day d, for d in 0,...,DAYS-1.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a boolean indicating if a flight occurs on day d.
# Convention: No flight on day 0.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: each day's city is within 0..(len(city_names)-1)
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))
s.add(flight[0] == False)

# For days 1 to DAYS-1, define flight indicator and allowed transitions.
for d in range(1, DAYS):
    # A flight occurs if today's city is different than yesterday's.
    s.add(flight[d] == (c[d] != c[d-1]))
    # If a flight occurs, the transition (c[d-1] -> c[d]) must be an allowed flight.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly REQUIRED_FLIGHTS flight-days.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function: inCityOnDay(d, target)
# On a flight day, day d "covers" both the previous (departure) city and the current (arrival) city.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits for each city.
# Day 0 gives 1 credit for city c[0].
# For days d >= 1:
#   - If no flight: add 1 credit for city c[d].
#   - If flight: add 1 credit for c[d-1] and 1 for c[d].
counts = [Int(f"count_{i}") for i in range(len(city_names))]
for city in range(len(city_names)):
    base = If(c[0] == city, 1, 0)
    daily_contrib = []
    for d in range(1, DAYS):
        daily_contrib.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == base + Sum(daily_contrib))
    # Enforce required day credits for city.
    s.add(counts[city] == required_credits[city])
    # Ensure each city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event constraints:

# 1. Relatives in Tallinn (city index 1) between day 18 and day 20.
# Corresponding to days indices 17, 18, 19.
s.add(Or([inCityOnDay(d, 1) for d in range(17, 20)]))

# 2. Meet friend in Milan (city index 5) between day 24 and day 26.
# Corresponding to day indices 23, 24, 25.
s.add(Or([inCityOnDay(d, 5) for d in range(23, 26)]))

# 3. Annual show in Riga (city index 8) from day 5 to day 8.
# Corresponding to day indices 4, 5, 6, 7.
for d in range(4, 8):
    s.add(inCityOnDay(d, 8))

# Solve the scheduling problem.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        info = f"Day {d+1:02d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = m[c[d-1]].as_long()
            arr = m[c[d]].as_long()
            info += f" (Flight: {city_names[dep]} -> {city_names[arr]})"
        print(info)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]:12s}: {m.evaluate(counts[i])}")
else:
    print("No solution found.")