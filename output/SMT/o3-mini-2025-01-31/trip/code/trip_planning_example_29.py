from z3 import *

# City indices and requirements:
# 0: Krakow   – 2 days; event: attend a wedding in Krakow between day 9 and day 10.
# 1: Dubrovnik – 7 days.
# 2: Frankfurt – 3 days.
city_names = ["Krakow", "Dubrovnik", "Frankfurt"]
req = [2, 7, 3]  # Total required day credits = 2+7+3 = 12

# Total base days = 10.
# On a day with no flight, the city gets 1 credit.
# On a flight day (when you fly from A to B on that day), both A and B get 1 credit.
# Hence, total credits = base days + (# flights).
# To reach 12 credits, we need exactly 2 flights (10 + 2 = 12).
# This partitions the trip into 3 segments (each segment corresponds to a visited city).
DAYS = 10

# Allowed direct flights (bidirectional unless indicated):
# Frankfurt and Krakow: (2,0) and (0,2)
# Dubrovnik and Frankfurt: (1,2) and (2,1)
allowed_flights = [
    (2,0), (0,2),
    (1,2), (2,1)
]

# Create Z3 variables:
# c[d] represents the base city on day d
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is True if a flight occurs on day d (for d>=1, day 0 no flight)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the starting day of a segment (either day 0 or a day with a flight)
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain: each day's base city must be in {0,1,2}
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 is always the start of a segment.
s.add(isSeg[0] == True)

# 3. For each day d>=1, define if a flight occurs and enforce allowed transitions.
for d in range(1, DAYS):
    # A flight happens if the city changes from day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs, the transition must follow one of the allowed flights.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly 2 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 2)

# 5. The starting city of each segment (day0 and any flight day) must be distinct,
# ensuring that each city is visited exactly once.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))
# Also enforce that every city appears as a segment's starting city.
for city in range(len(city_names)):
    s.add(Or([And(isSeg[d], c[d] == city) for d in range(DAYS)]))

# 6. Compute day contributions:
# Day 0 gives 1 credit to the city c[0].
# For d>=1:
#  - If a flight occurs on day d, then both the previous day's city and the current day's city get 1 credit.
#  - Otherwise, only the current day's city gets 1 credit.
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

# 7. Event constraint: Attend a wedding in Krakow (city 0)
# between day 9 and day 10 (i.e. indices 8 and 9).
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    # If flight occurs, consider both previous city's flight and current city.
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

wedding_event = [inCityOnDay(d, 0) for d in [8, 9]]
s.add(Or(wedding_event))

# Solve and print the itinerary
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