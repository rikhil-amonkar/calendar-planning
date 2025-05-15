from z3 import *

# City indices:
# 0: Lisbon      – required 2 days; event: attend a workshop in Lisbon between day 4 and day 5.
# 1: Dubrovnik   – required 5 days.
# 2: Copenhagen  – required 5 days.
# 3: Prague      – required 3 days.
# 4: Tallinn     – required 2 days; event: meet a friend in Tallinn between day 1 and day 2.
# 5: Stockholm   – required 4 days; event: attend a wedding in Stockholm between day 13 and day 16.
# 6: Split       – required 3 days.
# 7: Lyon        – required 2 days; event: attend an annual show in Lyon from day 18 to day 19.
city_names = ["Lisbon", "Dubrovnik", "Copenhagen", "Prague", "Tallinn", "Stockholm", "Split", "Lyon"]
required_credits = [2, 5, 5, 3, 2, 4, 3, 2]
# Total required credits = 2+5+5+3+2+4+3+2 = 26

# Total itinerary days:
DAYS = 19
# Credit rule: 
# - A day without a flight gives 1 credit to the day's city.
# - A day with a flight (city change) gives 1 credit for departure city and 1 for arrival city.
# Hence, total credits = DAYS + (# flight-days). We need 26 credits, so:
#   (# flight-days) = 26 - 19 = 7.
REQUIRED_FLIGHTS = 7

# Allowed direct flights (bidirectional):
# Dubrovnik and Stockholm          : (1,5) and (5,1)
# Lisbon and Copenhagen             : (0,2) and (2,0)
# Lisbon and Lyon                   : (0,7) and (7,0)
# Copenhagen and Stockholm          : (2,5) and (5,2)
# Copenhagen and Split              : (2,6) and (6,2)
# Prague and Stockholm              : (3,5) and (5,3)
# Tallinn and Stockholm             : (4,5) and (5,4)
# Prague and Lyon                   : (3,7) and (7,3)
# Lisbon and Stockholm              : (0,5) and (5,0)
# Prague and Lisbon                 : (3,0) and (0,3)
# Stockholm and Split               : (5,6) and (6,5)
# Prague and Copenhagen             : (3,2) and (2,3)
# Split and Lyon                    : (6,7) and (7,6)
# Copenhagen and Dubrovnik          : (2,1) and (1,2)
# Prague and Split                  : (3,6) and (6,3)
# Tallinn and Copenhagen            : (4,2) and (2,4)
# Tallinn and Prague                : (4,3) and (3,4)
allowed_flights = [
    (1,5), (5,1),
    (0,2), (2,0),
    (0,7), (7,0),
    (2,5), (5,2),
    (2,6), (6,2),
    (3,5), (5,3),
    (4,5), (5,4),
    (3,7), (7,3),
    (0,5), (5,0),
    (3,0), (0,3),
    (5,6), (6,5),
    (3,2), (2,3),
    (6,7), (7,6),
    (2,1), (1,2),
    (3,6), (6,3),
    (4,2), (2,4),
    (4,3), (3,4)
]

s = Solver()

# Variables:
# c[d]: city on day d (d = 0,..,DAYS-1), integer in {0,...,7}.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d]: Bool variable, True if a flight (city change) occurs on day d. 
# Convention: day 0 has no flight.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints for cities.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

s.add(flight[0] == False)  # No flight on day 0.

# For each day d=1,...,DAYS-1, define flight indicator and enforce allowed flight transitions.
for d in range(1, DAYS):
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly REQUIRED_FLIGHTS flight-days.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function: inCityOnDay(d, target)
# Returns an expression that is True if on day d the itinerary "includes" city target.
# On a flight day, both the departure (c[d-1]) and arrival (c[d]) count.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits for each city.
# Day 0 gives 1 credit for city c[0].
# For d>=1: if no flight, then day gives 1 credit for c[d]. If flight, then credit is given for both c[d-1] and c[d].
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
    # Each city must exactly get its required number of day credits.
    s.add(counts[city] == required_credits[city])
    # And ensure each city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event Constraints:

# 1. Workshop in Lisbon between day 4 and day 5.
# Days: indices 3 and 4 must include Lisbon (city 0) at least once.
s.add(Or(inCityOnDay(3, 0), inCityOnDay(4, 0)))

# 2. Meet a friend in Tallinn between day 1 and day 2.
# Days: indices 0 and 1 must include Tallinn (city 4) at least once.
s.add(Or(inCityOnDay(0, 4), inCityOnDay(1, 4)))

# 3. Wedding in Stockholm between day 13 and day 16.
# Days: indices 12, 13, 14, 15 – at least one of these must include Stockholm (city 5).
s.add(Or([inCityOnDay(d, 5) for d in range(12, 16)]))

# 4. Annual show in Lyon from day 18 to day 19.
# Days: indices 17 and 18 must include Lyon (city 7) at least once.
s.add(Or(inCityOnDay(17, 7), inCityOnDay(18, 7)))

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
        print(f"{city_names[i]:12s}: {m.evaluate(counts[i])}")
else:
    print("No solution found.")