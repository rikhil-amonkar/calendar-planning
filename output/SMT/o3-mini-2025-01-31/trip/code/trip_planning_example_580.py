from z3 import *

# City indices and requirements:
# 0: Paris      – 6 days
# 1: Oslo       – 5 days; event: visit relatives in Oslo between day 19 and day 23.
# 2: Porto      – 7 days
# 3: Geneva     – 7 days; event: attend a conference in Geneva on both day 1 and day 7.
# 4: Reykjavik  – 2 days
city_names = ["Paris", "Oslo", "Porto", "Geneva", "Reykjavik"]
req = [6, 5, 7, 7, 2]   # Total = 6+5+7+7+2 = 27

# Total base days = 23.
# Extra contributions come only on flight days (each flight day gives +1 extra for both the arrival and departure, compared to a normal day).
# Since every day provides 1 contribution, extra contributions = total req - base days = 27 - 23 = 4.
# Hence, exactly 4 flights are required.
# The trip is partitioned into 5 segments (each corresponding to one city).

DAYS = 23  # Days are indexed 0 .. 22 (representing days 1 .. 23)

# Allowed direct flights (bidirectional):
# - Paris and Oslo         : (0,1) and (1,0)
# - Geneva and Oslo        : (3,1) and (1,3)
# - Porto and Paris        : (2,0) and (0,2)
# - Geneva and Paris       : (3,0) and (0,3)
# - Geneva and Porto       : (3,2) and (2,3)
# - Paris and Reykjavik    : (0,4) and (4,0)
# - Reykjavik and Oslo     : (4,1) and (1,4)
# - Porto and Oslo         : (2,1) and (1,2)
allowed_flights = [
    (0,1), (1,0),
    (3,1), (1,3),
    (2,0), (0,2),
    (3,0), (0,3),
    (3,2), (2,3),
    (0,4), (4,0),
    (4,1), (1,4),
    (2,1), (1,2)
]

# Create Z3 variables:
# c[d] represents the base city for day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is True if there is a flight on day d (for d>=1)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a new segment (day 0 or a day when a flight occurs)
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain: Each day d, c[d] is in {0,...,4}
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 is always a segment start.
s.add(isSeg[0] == True)

# 3. For each day d>=1, determine if a flight happens, and if so enforce allowed flights.
for d in range(1, DAYS):
    # A flight occurs if the city changes from the previous day.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs, the transition must be one of the allowed direct flights.
    s.add(
        Implies(flight[d],
                Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
               )
    )

# 4. Exactly 4 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 4)

# 5. The starting city of each segment (day 0 and any flight day) must be unique.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally enforce that every city is visited:
for city in range(len(city_names)):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# 6. Compute the day contributions for each city.
# Day 0: add 1 for c[0].
# For day d>=1:
#   If flight occurs, add 1 to both c[d-1] (departure) and c[d] (arrival).
#   Otherwise, add 1 only for c[d].
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
    s.add(counts[city] == req[city])

# Helper function:
# inCityOnDay(d, target) returns a condition stating that on day d, the itinerary includes the target city.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Event constraints:
# (a) Visit relatives in Oslo (city 1) between day 19 and day 23 => day indices 18 to 22.
oslo_event = [inCityOnDay(d, 1) for d in range(18, 23)]
s.add(Or(oslo_event))

# (b) Attend a conference in Geneva (city 3) on day 1 and day 7.
# Day 1 is index 0, and day 7 is index 6.
s.add(inCityOnDay(0, 3))
s.add(inCityOnDay(6, 3))

# Solve and print the itinerary:
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_str = f"Day {d+1:2d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep_idx = m[c[d-1]].as_long()
            arr_idx = m[c[d]].as_long()
            day_str += f" (Flight: {city_names[dep_idx]} -> {city_names[arr_idx]})"
        print(day_str)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")