from z3 import *

# City indices and requirements:
# 0: Bucharest – 3 days.
# 1: Venice    – 5 days; event: attend a wedding in Venice between day 22 and day 26.
# 2: Prague   – 4 days.
# 3: Frankfurt – 5 days; event: attend an annual show in Frankfurt from day 12 to day 16.
# 4: Zurich   – 5 days.
# 5: Florence – 5 days.
# 6: Tallinn  – 5 days; event: meet friends at Tallinn between day 8 and day 12.
city_names = ["Bucharest", "Venice", "Prague", "Frankfurt", "Zurich", "Florence", "Tallinn"]
req = [3, 5, 4, 5, 5, 5, 5]  # Total required day credits = 3+5+4+5+5+5+5 = 32

# Total base days = 26.
# On a day with no flight, you get 1 credit for the city.
# On a flight day (if you fly from A to B on day X) both A and B get a credit.
# So total credits = 26 + (# flights).
# To meet 32 credits, we need exactly 6 flights.
# That partitions the itinerary into 7 segments (one per city).
DAYS = 26

# Allowed direct flights (note: we assume most flights are bidirectional unless
# noted otherwise; "from Zurich to Florence" is assumed as unidirectional (4,5)):
allowed_flights = [
    # Prague and Tallinn
    (2,6), (6,2),
    # Prague and Zurich
    (2,4), (4,2),
    # Florence and Prague
    (5,2), (2,5),
    # Frankfurt and Bucharest
    (3,0), (0,3),
    # Frankfurt and Venice
    (3,1), (1,3),
    # Prague and Bucharest
    (2,0), (0,2),
    # Bucharest and Zurich
    (0,4), (4,0),
    # Tallinn and Frankfurt
    (6,3), (3,6),
    # from Zurich to Florence (unidirectional: only allowed as (4,5))
    (4,5),
    # Frankfurt and Zurich
    (3,4), (4,3),
    # Zurich and Venice
    (4,1), (1,4),
    # Florence and Frankfurt
    (5,3), (3,5),
    # Prague and Frankfurt
    (2,3), (3,2),
    # Tallinn and Zurich
    (6,4), (4,6)
]

# Create Z3 variables:
# c[d] is the base city on day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Bool which is true when a flight occurs on day d.
# (For d=0, there is no flight since that's our starting day.)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is true if day d is the start of a new segment (either day0 or when a flight occurs).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain constraints: each day's base city must be one of the 7 cities (0..6).
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 always starts a segment.
s.add(isSeg[0] == True)

# 3. For each day d>=1: determine if a flight occurs and enforce allowed flight transitions.
for d in range(1, DAYS):
    # A flight occurs on day d if the city at day d differs from day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs, the transition must be an allowed direct flight.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly 6 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 6)

# 5. The starting base city of each segment (day0 and any flight day) must be distinct.
# This guarantees that each city is visited exactly once.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))
# Also enforce that every city is used as a segment start.
for city in range(len(city_names)):
    s.add(Or([And(isSeg[d], c[d] == city) for d in range(DAYS)]))

# 6. Compute day contributions for each city.
# Day 0 immediately gives 1 credit for c[0].
# For each day d>=1:
#   - if a flight occurs, then both the previous day's city and the current day's city get a credit.
#   - if no flight occurs, then only the current day's city gets a credit.
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
    s.add(counts[city] == req[city])

# Helper: on day d, the itinerary "includes" target city if:
# on day 0, if c[0] equals target, or on day d>=1:
# if a flight occurs then either the departure or arrival equals the target,
# else just check c[d].
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Event constraints:
# (a) Wedding in Venice (city 1) between day 22 and day 26 (indices 21 to 25).
wedding_event = [inCityOnDay(d, 1) for d in range(21, 26)]
s.add(Or(wedding_event))

# (b) Annual show in Frankfurt (city 3) from day 12 to day 16 (indices 11 to 15).
frankfurt_event = [inCityOnDay(d, 3) for d in range(11, 16)]
s.add(Or(frankfurt_event))

# (c) Meeting friends at Tallinn (city 6) between day 8 and day 12 (indices 7 to 11).
tallinn_event = [inCityOnDay(d, 6) for d in range(7, 12)]
s.add(Or(tallinn_event))

# Solve the model and output a solution.
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