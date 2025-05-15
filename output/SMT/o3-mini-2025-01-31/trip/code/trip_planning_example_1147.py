from z3 import *

# City indices:
# 0: Brussels   – required 3 days
# 1: Helsinki   – required 3 days
# 2: Split      – required 4 days
# 3: Dubrovnik  – required 2 days
# 4: Istanbul   – required 5 days; event: attend an annual show in Istanbul from day 1 to day 5.
# 5: Milan      – required 4 days
# 6: Vilnius    – required 5 days; event: attend a workshop in Vilnius between day 18 and day 22.
# 7: Frankfurt  – required 3 days; event: attend a wedding in Frankfurt between day 16 and day 18.
city_names = ["Brussels", "Helsinki", "Split", "Dubrovnik", "Istanbul", "Milan", "Vilnius", "Frankfurt"]
required_credits = [3, 3, 4, 2, 5, 4, 5, 3]
# Total required day credits = 3+3+4+2+5+4+5+3 = 29

# Total itinerary days:
DAYS = 22
# Credit accounting:
# - A non-flight day gives 1 credit for that day’s city.
# - A flight day (when the city changes) gives 1 credit for the departure city and 1 for the arrival city.
# Total credits = DAYS + (# flight-days). To have 29 credits: (# flight-days) = 29 - 22 = 7.
REQUIRED_FLIGHTS = 7

# Allowed direct flights (bidirectional unless indicated as a one-way flight):
# Milan and Frankfurt
#   (Milan, Frankfurt) and (Frankfurt, Milan): (5,7) and (7,5)
# Split and Frankfurt
#   (Split, Frankfurt) and (Frankfurt, Split): (2,7) and (7,2)
# Milan and Split
#   (Milan, Split) and (Split, Milan): (5,2) and (2,5)
# Brussels and Vilnius
#   (Brussels, Vilnius) and (Vilnius, Brussels): (0,6) and (6,0)
# Brussels and Helsinki
#   (Brussels, Helsinki) and (Helsinki, Brussels): (0,1) and (1,0)
# Istanbul and Brussels
#   (Istanbul, Brussels) and (Brussels, Istanbul): (4,0) and (0,4)
# Milan and Vilnius
#   (Milan, Vilnius) and (Vilnius, Milan): (5,6) and (6,5)
# Brussels and Milan
#   (Brussels, Milan) and (Milan, Brussels): (0,5) and (5,0)
# Istanbul and Helsinki
#   (Istanbul, Helsinki) and (Helsinki, Istanbul): (4,1) and (1,4)
# Helsinki and Vilnius
#   (Helsinki, Vilnius) and (Vilnius, Helsinki): (1,6) and (6,1)
# Helsinki and Dubrovnik
#   (Helsinki, Dubrovnik) and (Dubrovnik, Helsinki): (1,3) and (3,1)
# Split and Vilnius
#   (Split, Vilnius) and (Vilnius, Split): (2,6) and (6,2)
# from Dubrovnik to Istanbul (one-way only)
#   (Dubrovnik, Istanbul): (3,4)
# Istanbul and Milan
#   (Istanbul, Milan) and (Milan, Istanbul): (4,5) and (5,4)
# Helsinki and Frankfurt
#   (Helsinki, Frankfurt) and (Frankfurt, Helsinki): (1,7) and (7,1)
# Istanbul and Vilnius
#   (Istanbul, Vilnius) and (Vilnius, Istanbul): (4,6) and (6,4)
# Split and Helsinki
#   (Split, Helsinki) and (Helsinki, Split): (2,1) and (1,2)
# Milan and Helsinki
#   (Milan, Helsinki) and (Helsinki, Milan): (5,1) and (1,5)
# Istanbul and Frankfurt
#   (Istanbul, Frankfurt) and (Frankfurt, Istanbul): (4,7) and (7,4)
# from Brussels to Frankfurt (one-way only)
#   (Brussels, Frankfurt): (0,7)
# Dubrovnik and Frankfurt
#   (Dubrovnik, Frankfurt) and (Frankfurt, Dubrovnik): (3,7) and (7,3)
# Frankfurt and Vilnius
#   (Frankfurt, Vilnius) and (Vilnius, Frankfurt): (7,6) and (6,7)
allowed_flights = [
    (5,7), (7,5),
    (2,7), (7,2),
    (5,2), (2,5),
    (0,6), (6,0),
    (0,1), (1,0),
    (4,0), (0,4),
    (5,6), (6,5),
    (0,5), (5,0),
    (4,1), (1,4),
    (1,6), (6,1),
    (1,3), (3,1),
    (2,6), (6,2),
    (3,4),          # one-way: from Dubrovnik to Istanbul
    (4,5), (5,4),
    (1,7), (7,1),
    (4,6), (6,4),
    (2,1), (1,2),
    (5,1), (1,5),
    (4,7), (7,4),
    (0,7),          # one-way: from Brussels to Frankfurt
    (3,7), (7,3),
    (7,6), (6,7)
]

# Create Z3 solver instance.
s = Solver()

# Variables:
# c[d] is the "base" city on day d (for d = 0,1,...,DAYS-1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean variable which indicates whether a flight takes place on day d.
# By convention, day 0 has no flight.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: each day's city is in the set {0,..,7}.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# Day 0: no flight.
s.add(flight[0] == False)

# For days 1..DAYS-1, define flight indicator and enforce allowed flight transitions.
for d in range(1, DAYS):
    # A flight occurs on day d if the city on day d differs from that on day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    # If a flight occurs, then the transition (c[d-1] -> c[d]) must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly REQUIRED_FLIGHTS flight-days.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function: inCityOnDay(d, target)
# Returns an expression that is true if on day d, the itinerary "includes" the city target.
# For a flight day, both the departure (c[d-1]) and arrival (c[d]) count.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits for each city.
# Day 0 gives 1 credit for the base city c[0].
# For each subsequent day d (from 1 to DAYS-1):
# - If there is no flight, award 1 credit to c[d].
# - If there is a flight, award 1 credit for the departure (c[d-1]) and 1 for arrival (c[d]).
counts = [Int(f"count_{i}") for i in range(len(city_names))]
for city in range(len(city_names)):
    base_credit = If(c[0] == city, 1, 0)
    daily = []
    for d in range(1, DAYS):
        daily.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == base_credit + Sum(daily))
    # Enforce that the computed credits equal the required days for the city.
    s.add(counts[city] == required_credits[city])
    # Ensure each city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event Constraints:

# 1. Annual show in Istanbul from day 1 to day 5.
# Days 1 to 5 correspond to indices 0, 1, 2, 3, 4.
s.add(Or([inCityOnDay(d, 4) for d in range(0, 5)]))

# 2. Workshop in Vilnius between day 18 and day 22.
# Days 18 to 22 correspond to indices 17, 18, 19, 20, 21.
s.add(Or([inCityOnDay(d, 6) for d in range(17, 22)]))

# 3. Wedding in Frankfurt between day 16 and day 18.
# Days 16 to 18 correspond to indices 15, 16, 17.
s.add(Or([inCityOnDay(d, 7) for d in range(15, 18)]))

# Solve the scheduling problem.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_str = f"Day {d+1:02d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = m[c[d-1]].as_long()
            arr = m[c[d]].as_long()
            day_str += f" (Flight: {city_names[dep]} -> {city_names[arr]})"
        print(day_str)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]:10s}: {m.evaluate(counts[i])}")
else:
    print("No solution found.")