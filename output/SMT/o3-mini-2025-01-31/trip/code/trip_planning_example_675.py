from z3 import *

# City indices and requirements:
# 0: Dubrovnik – 4 days.
# 1: Split     – 3 days.
# 2: Milan     – 3 days; event: wedding in Milan between day 11 and day 13.
# 3: Porto     – 4 days.
# 4: Krakow    – 2 days; event: meet friends in Krakow between day 8 and day 9.
# 5: Munich    – 5 days; event: annual show in Munich between day 4 and day 8.
city_names = ["Dubrovnik", "Split", "Milan", "Porto", "Krakow", "Munich"]
req = [4, 3, 3, 4, 2, 5]  # Total required day credits = 4+3+3+4+2+5 = 21

# Total base days:
DAYS = 16
# On a day with no flight, the city gets 1 credit.
# On a flight day, if you fly from city A to city B on that day,
# both A and B receive 1 credit.
# Total credits = 16 + (# flights).
# We require 21 credits, thus we need exactly 5 flights.
REQUIRED_FLIGHTS = 5

# Allowed direct flights as (from, to) pairs.
allowed_flights = [
    # Munich and Porto
    (5, 3), (3, 5),
    # Split and Milan
    (1, 2), (2, 1),
    # Milan and Porto
    (2, 3), (3, 2),
    # Munich and Krakow
    (5, 4), (4, 5),
    # Munich and Milan
    (5, 2), (2, 5),
    # Dubrovnik and Munich
    (0, 5), (5, 0),
    # Krakow and Split
    (4, 1), (1, 4),
    # Krakow and Milan
    (4, 2), (2, 4),
    # Munich and Split
    (5, 1), (1, 5)
]

# Create Z3 solver.
s = Solver()

# Create variables:
# c[d] is the "base" city on day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is True if a flight occurs on day d. Day 0 has no flight.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a new segment.
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

# 1. Domain constraints for day's city.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 is always a segment start (and no flight on day 0).
s.add(flight[0] == False)
s.add(isSeg[0] == True)

# 3. For day d>=1, determine if a flight occurs and set segment markers.
for d in range(1, DAYS):
    # Flight if city changes from previous day.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    
    # If a flight occurs on day d, then the transition must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly REQUIRED_FLIGHTS flights in days 1..(DAYS-1)
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == REQUIRED_FLIGHTS)

# 5. Distinct Segment constraint:
# The "base" city for each segment (day 0 and any day with a flight) must be distinct.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))
# Also, every city must appear as a segment start.
for city in range(len(city_names)):
    s.add(Or([And(isSeg[d], c[d] == city) for d in range(DAYS)]))

# 6. Compute day contributions per city.
# Day 0 contributes 1 credit for city c[0].
# For each day d>=1, if there's no flight, add 1 credit to c[d];
# if there's a flight, add 1 credit to both c[d-1] and c[d].
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
    # Enforce required day credits.
    s.add(counts[city] == req[city])

# 7. Event constraints:
# Helper function: expression that is true if on day d the itinerary includes 'target'.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# (a) Wedding in Milan (city 2) between day 11 and day 13 -> indices 10, 11, 12.
milan_wedding = [inCityOnDay(d, 2) for d in [10, 11, 12]]
s.add(Or(milan_wedding))

# (b) Meeting friends in Krakow (city 4) between day 8 and day 9 -> indices 7 and 8.
krakow_meet = [inCityOnDay(d, 4) for d in [7, 8]]
s.add(Or(krakow_meet))

# (c) Annual show in Munich (city 5) from day 4 to day 8 -> indices 3,4,5,6,7.
munich_show = [inCityOnDay(d, 5) for d in range(3, 8)]
s.add(Or(munich_show))

# Solve the model
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city = m[c[d]].as_long()
        day_line = f"Day {d+1:2d}: {city_names[city]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = m[c[d-1]].as_long()
            arr = city
            day_line += f" (Flight: {city_names[dep]} -> {city_names[arr]})"
        print(day_line)
    
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]:10s}: {m.evaluate(counts[i])}")
else:
    print("No solution found")