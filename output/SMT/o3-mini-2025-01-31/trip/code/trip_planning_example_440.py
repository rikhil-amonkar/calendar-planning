from z3 import *

# City indices and requirements:
# 0: Split      – required 2 days.
# 1: Helsinki   – required 2 days.
# 2: Reykjavik  – required 3 days; event: attend wedding in Reykjavik between day 10 and day 12.
# 3: Vilnius    – required 3 days; event: visit relatives in Vilnius between day 7 and day 9.
# 4: Geneva     – required 6 days.
city_names = ["Split", "Helsinki", "Reykjavik", "Vilnius", "Geneva"]
required_credits = [2, 2, 3, 3, 6]
# Total required credits = 2 + 2 + 3 + 3 + 6 = 16

# Total itinerary days:
DAYS = 12
# Flight rule: each day with no flight provides 1 credit, whereas on a flight day you get 1 credit from the departure and 1 from the arrival.
# Hence total credits = DAYS + (# flight-days). We need 16 total credits.
# => (# flight-days) = 16 - 12 = 4.
REQUIRED_FLIGHTS = 4

# Allowed direct flights:
# "Split and Helsinki"      : (0,1) and (1,0)
# "Geneva and Split"        : (4,0) and (0,4)
# "Geneva and Helsinki"     : (4,1) and (1,4)
# "Helsinki and Reykjavik"  : (1,2) and (2,1)
# "Vilnius and Helsinki"    : (3,1) and (1,3)
# "Split and Vilnius"       : (0,3) and (3,0)
allowed_flights = [
    (0,1), (1,0),
    (4,0), (0,4),
    (4,1), (1,4),
    (1,2), (2,1),
    (3,1), (1,3),
    (0,3), (3,0)
]

# Create Z3 solver
s = Solver()

# Variables:
# c[d] is the city index on day d (d = 0,...,DAYS - 1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is Boolean indicating whether a flight occurs on day d.
# By convention, no flight happens on day 0.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: each day, the city index must be one of the defined cities.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))
s.add(flight[0] == False)

# For days 1...DAYS-1, set flight indicator and enforce allowed transitions.
for d in range(1, DAYS):
    # A flight occurs if the city changes from day d-1 to day d.
    s.add(flight[d] == (c[d] != c[d-1]))
    # If there is a flight, enforce that the transition is allowed.
    s.add(Implies(flight[d], 
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly REQUIRED_FLIGHTS flight days.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper: inCityOnDay(d, target)
# On a flight day, both the departure city and arrival city "cover" day d.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits for each city:
# - Day 0 provides 1 credit to the city c[0].
# - For each day d >= 1:
#     if no flight: day d gives 1 credit for city c[d]
#     if there's a flight: day d gives 1 credit for c[d-1] and 1 for c[d]
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
    # Enforce city day requirements.
    s.add(counts[city] == required_credits[city])
    # Also ensure that every city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event constraints:

# 1. Wedding in Reykjavik (city 2) between day 10 and day 12.
# Days 10, 11, 12 correspond to indices 9, 10, 11.
s.add(Or([inCityOnDay(d, 2) for d in range(9, 12)]))

# 2. Visit relatives in Vilnius (city 3) between day 7 and day 9.
# Days 7, 8, 9 correspond to indices 6, 7, 8.
s.add(Or([inCityOnDay(d, 3) for d in range(6, 9)]))

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
        print(f"{city_names[i]:10s}: {m.evaluate(counts[i])}")
else:
    print("No solution found.")