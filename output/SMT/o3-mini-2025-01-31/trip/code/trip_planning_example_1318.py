from z3 import *

# City indices and requirements:
# 0: Oslo       – required 2 days; event: meet a friend in Oslo between day 24 and day 25.
# 1: Helsinki   – required 2 days.
# 2: Edinburgh  – required 3 days.
# 3: Riga       – required 2 days.
# 4: Tallinn    – required 5 days; event: attend a wedding in Tallinn between day 4 and day 8.
# 5: Budapest   – required 5 days.
# 6: Vilnius    – required 5 days.
# 7: Porto      – required 5 days.
# 8: Geneva     – required 4 days.
city_names = ["Oslo", "Helsinki", "Edinburgh", "Riga", "Tallinn", "Budapest", "Vilnius", "Porto", "Geneva"]
required_credits = [2, 2, 3, 2, 5, 5, 5, 5, 4]
# Total required credits = 2+2+3+2+5+5+5+5+4 = 33

# Total itinerary days:
DAYS = 25
# Credit rule: Each day gives 1 credit for the city on that day,
# but if a flight is taken on a day then both the departure and the arrival city are counted.
# That is, total credits = DAYS + (# flight-days).
# We thus need:
#   DAYS + (# flight-days) = 33  => # flight-days = 33 - 25 = 8.
REQUIRED_FLIGHTS = 8

# Allowed direct flights between cities.
# Bidirectional flights are listed in both directions.
# Unidirectional flights are listed only one way.
allowed_flights = [
    # Porto and Oslo
    (7, 0), (0, 7),
    # Edinburgh and Budapest
    (2, 5), (5, 2),
    # Edinburgh and Geneva
    (2, 8), (8, 2),
    # from Riga to Tallinn (unidirectional)
    (3, 4),
    # Edinburgh and Porto
    (2, 7), (7, 2),
    # Vilnius and Helsinki
    (6, 1), (1, 6),
    # from Tallinn to Vilnius (unidirectional)
    (4, 6),
    # Riga and Oslo
    (3, 0), (0, 3),
    # Geneva and Oslo
    (8, 0), (0, 8),
    # Edinburgh and Oslo
    (2, 0), (0, 2),
    # Edinburgh and Helsinki
    (2, 1), (1, 2),
    # Vilnius and Oslo
    (6, 0), (0, 6),
    # Riga and Helsinki
    (3, 1), (1, 3),
    # Budapest and Geneva
    (5, 8), (8, 5),
    # Helsinki and Budapest
    (1, 5), (5, 1),
    # Helsinki and Oslo
    (1, 0), (0, 1),
    # Edinburgh and Riga
    (2, 3), (3, 2),
    # Tallinn and Helsinki
    (4, 1), (1, 4),
    # Geneva and Porto
    (8, 7), (7, 8),
    # Budapest and Oslo
    (5, 0), (0, 5),
    # Helsinki and Geneva
    (1, 8), (8, 1),
    # Tallinn and Oslo
    (4, 0), (0, 4),
    # from Riga to Vilnius (unidirectional)
    (3, 6)
]

# Create the Z3 solver
s = Solver()

# Define variables:
# c[d] is the city (index) on day d, for d = 0, 1, ..., DAYS-1.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean that indicates if a flight (transition) occurs on day d.
# By convention, day 0 is not a flight day.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# City domain constraints: each day's city is in 0..8.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))
s.add(flight[0] == False)

# For day 1 to DAYS-1, determine the flight indicator and enforce allowed flight transitions.
for d in range(1, DAYS):
    # A flight occurs on day d if the city changes from day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    # If a flight happens on day d, then the transition (c[d-1] -> c[d]) must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Exactly REQUIRED_FLIGHTS days have a flight.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function: inCityOnDay(d, target)
# This returns a condition that day d "includes" the target city.
# On a flight day, both the departure and arrival cities count.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits for each city.
# Day 0 contributes 1 credit to the city c[0].
# For each day d>=1:
#   - If there is no flight, add 1 credit for c[d].
#   - If there is a flight, add 1 credit for c[d-1] and 1 for c[d].
counts = [Int(f"count_{i}") for i in range(len(city_names))]
for city in range(len(city_names)):
    base = If(c[0] == city, 1, 0)
    daily_counts = []
    for d in range(1, DAYS):
        daily_counts.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == base + Sum(daily_counts))
    # Enforce that the required credits for each city are met.
    s.add(counts[city] == required_credits[city])
    # Also ensure that each city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event constraints:

# 1. Meet a friend in Oslo (city 0) between day 24 and day 25.
# Days 24 and 25 correspond to indices 23 and 24.
s.add(Or(inCityOnDay(23, 0), inCityOnDay(24, 0)))

# 2. Attend a wedding in Tallinn (city 4) between day 4 and day 8.
# That means at least one day among days 4-8 (indices 3,4,5,6,7) must "include" Tallinn.
s.add(Or([inCityOnDay(d, 4) for d in range(3, 8)]))

# Solve the scheduling problem.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_info = f"Day {d+1:02d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = m[c[d-1]].as_long()
            arr = m[c[d]].as_long()
            day_info += f" (Flight: {city_names[dep]} -> {city_names[arr]})"
        print(day_info)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]:10s}: {m.evaluate(counts[i])}")
else:
    print("No solution found.")