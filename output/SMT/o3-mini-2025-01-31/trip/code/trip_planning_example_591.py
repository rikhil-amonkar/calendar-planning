from z3 import *

# City indices and requirements:
# 0: Stuttgart  – 2 days.
# 1: Bucharest  – 2 days.
# 2: Geneva     – 4 days; event: visit relatives in Geneva between day 1 and day 4.
# 3: Valencia   – 6 days.
# 4: Munich     – 7 days; event: meet friends at Munich between day 4 and day 10.
city_names = ["Stuttgart", "Bucharest", "Geneva", "Valencia", "Munich"]
req = [2, 2, 4, 6, 7]  # Total required day credits = 2+2+4+6+7 = 21

# Total base days = 17.
# On a day with no flight, only 1 city gets 1 credit.
# When a flight is taken, both the departure and arrival get a credit.
# Total credits = base days + (# flights).
# Thus we need (# flights) = 21 - 17 = 4 flights.
# Then there will be 5 segments (one per city).
DAYS = 17

# Allowed direct flights (bidirectional):
# Geneva and Munich      -> (Geneva, Munich): (2,4) and (4,2)
# Munich and Valencia    -> (Munich, Valencia): (4,3) and (3,4)
# Bucharest and Valencia -> (Bucharest, Valencia): (1,3) and (3,1)
# Munich and Bucharest   -> (Munich, Bucharest): (4,1) and (1,4)
# Valencia and Stuttgart -> (Valencia, Stuttgart): (3,0) and (0,3)
# Geneva and Valencia    -> (Geneva, Valencia): (2,3) and (3,2)
allowed_flights = [
    (2,4), (4,2),
    (4,3), (3,4),
    (1,3), (3,1),
    (4,1), (1,4),
    (3,0), (0,3),
    (2,3), (3,2)
]

# Create Z3 variables:
# c[d]: base city on day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d]: True if a flight occurs on day d (for d>=1; day 0 no flight).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d]: True if day d is the start of a new segment (day 0 or day with a flight).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain constraints: each day's city must be in {0,...,4}.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 is the start of a segment.
s.add(isSeg[0] == True)

# 3. For days d>=1, flight criteria and allowed transitions.
for d in range(1, DAYS):
    # A flight occurs if the city changes.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # When a flight occurs, ensure that the transition is allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly 4 flights in total.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 4)

# 5. Distinct segment constraint:
# The starting city of each segment (day 0 and days with a flight) must be unique.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Also ensure that every city is visited as a segment start.
for city in range(len(city_names)):
    s.add(Or([And(isSeg[d], c[d] == city) for d in range(DAYS)]))

# 6. Compute day contributions for each city.
# Day 0 contributes 1 credit for c[0]. Then for each day d>=1:
#   - If flight occurs, add credit to both departure and arrival.
#   - If no flight occurs, add credit for current city's day.
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

# Helper function: on day d, determine if itinerary "includes" a target city.
# If a flight occurs on day d, then both the departure (previous day) and the arrival (day d)
# count as being in that city.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Event constraints:
# (a) Relatives in Geneva (city 2) between day 1 and day 4.
#     That is, for some day d in indices 0 to 3, we must include Geneva.
geneva_event = [inCityOnDay(d, 2) for d in range(0, 4)]
s.add(Or(geneva_event))

# (b) Meet friends in Munich (city 4) between day 4 and day 10.
#     That is, for some day d in indices 3 to 9, the itinerary must include Munich.
munich_event = [inCityOnDay(d, 4) for d in range(3, 10)]
s.add(Or(munich_event))

# Solve the model:
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_str = f"Day {d+1:2d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[city_idx]
            day_str += f" (Flight: {dep} -> {arr})"
        print(day_str)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")