from z3 import *

# City indices and requirements:
# 0: Stuttgart  – 6 days; event: meet a friend in Stuttgart between day 1 and day 6.
# 1: Seville    – 7 days.
# 2: Manchester – 4 days.
city_names = ["Stuttgart", "Seville", "Manchester"]
req = [6, 7, 4]  # Total required day credits = 6+7+4 = 17

# Total base days = 15.
# On a day with no flight, that day's base city gets 1 credit.
# On a flight day, both the departure and arrival cities get a credit.
# Thus, total credits = base days + (# flights) = 15 + (# flights).
# To achieve 17 total credits, we need exactly 2 flights.
# This partitions the trip into 3 segments (each corresponding to one city).
DAYS = 15

# Allowed direct flights (bidirectional):
# Manchester and Seville -> (Manchester, Seville): (2,1) and (Seville, Manchester): (1,2)
# Stuttgart and Manchester -> (Stuttgart, Manchester): (0,2) and (Manchester, Stuttgart): (2,0)
allowed_flights = [
    (2,1), (1,2),
    (0,2), (2,0)
]

# Create Z3 variables:
# c[d] is the base city on day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is True if a flight occurs on day d (d>=1; day 0 has no flight).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d marks the start of a new segment (day 0 or when a flight occurs).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain: each day's base city must be one of the 3 cities.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 always starts a segment.
s.add(isSeg[0] == True)

# 3. For each day d>=1, define flight occurrence and allowed flight transitions.
for d in range(1, DAYS):
    # A flight occurs if the base city changes.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs, then the transition must be one of the allowed flights.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly 2 flights in total.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 2)

# 5. The starting base cities of each segment (day 0 and days with a flight) must be distinct.
#    This ensures that each city is visited exactly once.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Ensure that every city is visited as a segment start.
for city in range(len(city_names)):
    s.add(Or([And(isSeg[d], c[d] == city) for d in range(DAYS)]))

# 6. Compute day contributions for each city.
# Day 0 counts for c[0].
# For each day d>=1:
#   - If a flight occurs on day d, then both the previous day's city and the current day's city get a credit.
#   - If no flight occurs, then only the current day's city gets a credit.
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

# Helper: on day d, check if the itinerary "includes" a target city.
# If a flight occurs on day d, then both the departure (day d-1) and the arrival (day d) are considered.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Event constraints:
# (a) Meet a friend in Stuttgart (city 0) between day 1 and day 6 (indices 0 to 5).
stuttgart_event = [inCityOnDay(d, 0) for d in range(0, 6)]
s.add(Or(stuttgart_event))

# Solve the model and output the itinerary.
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