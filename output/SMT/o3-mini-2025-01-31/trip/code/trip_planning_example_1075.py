from z3 import *

# Cities (indices and names):
# 0: Vienna       (4 days)
# 1: Lyon         (3 days)
# 2: Edinburgh    (4 days; annual show between day 5 and 8)
# 3: Reykjavik    (5 days)
# 4: Stuttgart    (5 days)
# 5: Manchester   (2 days)
# 6: Split        (5 days; wedding between day 19 and day 23)
# 7: Prague       (4 days)
city_names = ["Vienna", "Lyon", "Edinburgh", "Reykjavik", "Stuttgart", "Manchester", "Split", "Prague"]

# Required day counts for each city:
req = [4, 3, 4, 5, 5, 2, 5, 4]

# Allowed direct flights.
# The flights listed below are derived from the problem statement.
# For bidirectional connections, both ordered pairs are added.
# For unidirectional ones ("from X to Y"), only that order is allowed.
allowed_flights = [
    # from Reykjavik to Stuttgart
    (3, 4),
    # Stuttgart and Split
    (4, 6), (6, 4),
    # Stuttgart and Vienna
    (4, 0), (0, 4),
    # Prague and Manchester
    (7, 5), (5, 7),
    # Edinburgh and Prague
    (2, 7), (7, 2),
    # from Manchester to Split
    (5, 6),
    # Prague and Vienna
    (7, 0), (0, 7),
    # Vienna and Manchester
    (0, 5), (5, 0),
    # Prague and Split
    (7, 6), (6, 7),
    # Vienna and Lyon
    (0, 1), (1, 0),
    # Stuttgart and Edinburgh
    (4, 2), (2, 4),
    # Split and Lyon
    (6, 1), (1, 6),
    # Stuttgart and Manchester
    (4, 5), (5, 4),
    # Prague and Lyon
    (7, 1), (1, 7),
    # Reykjavik and Vienna
    (3, 0), (0, 3),
    # Prague and Reykjavik
    (7, 3), (3, 7),
    # Vienna and Split
    (0, 6), (6, 0)
]

# Total itinerary days.
DAYS = 25

# Total "day contributions" required (taking into account flights counting twice):
# sum(req) = 4+3+4+5+5+2+5+4 = 32.
# In our model, the total contributions = (# base days) + (# flight days)
# = 25 + f. Hence we require f = 32 - 25 = 7 flight days.
#
# When a flight occurs on day d (for d>=1), the traveler is considered to be in the departure city (c[d-1])
# and in the arrival city (c[d]) on that day.
# We use 25 “base city” variables (c[0]..c[24]), with extra contribution on flight days.
# With exactly 7 flight days, there are 8 segments. We require these segments (the city on day 0 plus
# each day when a flight occurs) to be all distinct, ensuring the plan uses all 8 cities.

# Create Z3 variables:
# c[d] is the "base city" on day d (0-indexed, representing day d+1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean flag indicating that on day d (for d>=1) a flight occurs (i.e. c[d] != c[d-1]).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d starts a segment (day 0 always, and every day when a flight occurs).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Ensure each c[d] is a valid city index.
for d in range(DAYS):
    s.add(And(c[d] >= 0, c[d] < 8))

# Day 0 is always a segment start.
s.add(isSeg[0] == True)

# For days 1 to 24, define the flight indicator and allowed flight constraints.
for d in range(1, DAYS):
    # A flight occurs on day d if the city changes compared to day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs on day d, then the pair (c[d-1], c[d]) must be one of the allowed flights.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 )
         )

# Exactly 7 flight days must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 7)

# The cities at the beginning of each segment (i.e. day 0 and every flight day) must be distinct.
for d1 in range(DAYS):
    for d2 in range(d1+1, DAYS):
        s.add(Implies(And(isSeg[d1], isSeg[d2]), c[d1] != c[d2]))

# Optionally, enforce that each city appears at least once in the itinerary.
for city in range(8):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Compute the "day contributions" for each city:
# On day 0, the traveler is in city c[0] (1 count).
# For each day d from 1 to 24:
#   - If there is no flight on day d, only c[d] gets 1 count.
#   - If there is a flight on day d, then both the departure city (c[d-1]) and the arrival city (c[d]) get 1 count.
counts = [Int(f"count_{city}") for city in range(8)]
for city in range(8):
    base = If(c[0] == city, 1, 0)
    contribs = []
    for d in range(1, DAYS):
        contrib = If(flight[d],
                     If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
                     If(c[d] == city, 1, 0))
        contribs.append(contrib)
    s.add(counts[city] == base + Sum(contribs))
    s.add(counts[city] == req[city])

# Helper function: "inCityOnDay" returns a constraint that the itinerary on day d includes the target city.
# On day 0, it's simply c[0] == target.
# On day d>=1, if a flight occurs, the traveler is in both c[d-1] and c[d]; otherwise, just in c[d].
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Additional scheduling constraints:
# 1. Edinburgh annual show (city 2) from day 5 to day 8:
#    Ensure that at least one day among days 5,6,7,8 (indices 4 to 7) includes Edinburgh.
ed_show = [inCityOnDay(d, 2) for d in range(4, 8)]
s.add(Or(ed_show))

# 2. Wedding in Split (city 6) between day 19 and day 23:
#    Ensure that at least one day among days 19,20,21,22,23 (indices 18 to 22) includes Split.
wedding_split = [inCityOnDay(d, 6) for d in range(18, 23)]
s.add(Or(wedding_split))

# Check for a solution.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        day_str = f"Day {d+1:2d}: In {city_names[m[c[d]].as_long()]}"
        if d >= 1 and m.evaluate(flight[d]):
            day_str += f" (Flight: {city_names[m[c[d-1]].as_long()]} -> {city_names[m[c[d]].as_long()]})"
        print(day_str)
    print("\nCity day counts:")
    for city in range(8):
        print(f"{city_names[city]}: {m.evaluate(counts[city])}")
else:
    print("No solution found")