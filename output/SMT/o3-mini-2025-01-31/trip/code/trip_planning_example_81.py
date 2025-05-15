from z3 import *

# We have 3 cities:
# 0: Mykonos – 6 days; event: attend a conference in Mykonos on day 4 and day 9.
# 1: Budapest– 3 days.
# 2: Hamburg – 2 days.
city_names = ["Mykonos", "Budapest", "Hamburg"]
req = [6, 3, 2]  # Total required credits = 6+3+2 = 11

# Total base days = 9.
# On a non-flight day, the day’s base city gets 1 credit.
# On a flight day, both the departure and arrival cities get 1 credit.
# Hence, total credits = base days + (# flights).
# We therefore need 11 - 9 = 2 flights.
# With 2 flights, the itinerary is partitioned into 3 segments (one per city).

DAYS = 9

# Allowed direct flights (bidirectional):
#   Budapest and Mykonos: (1, 0) and (0, 1)
#   Hamburg and Budapest: (2, 1) and (1, 2)
allowed_flights = [
    (1, 0), (0, 1),
    (2, 1), (1, 2)
]

# Create Z3 variables:
# c[d] is the base city (the city you are "in") on day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is True if a flight occurs on day d (d>=1; day 0 has no flight).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d marks the start of a new segment (day 0 or when a flight occurs).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain: Each day's base city must be one of 0,1,2.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 always starts a segment.
s.add(isSeg[0] == True)

# 3. For each day d (d>=1), define flight occurrence:
#    A flight occurs if the base city changes.
#    When a flight occurs, the city transition must be an allowed direct flight.
for d in range(1, DAYS):
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly 2 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 2)

# 5. The starting city of each segment (day0 and any flight day) must be distinct,
#    ensuring that each city is visited exactly once.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally enforce that every city is visited.
for city in range(len(city_names)):
    s.add(Or([And(isSeg[d], c[d] == city) for d in range(DAYS)]))

# 6. Compute day contributions for each city.
#    Day 0 contributes 1 to its base city.
#    For each day d>=1:
#       - If a flight occurs, both the previous day's city and the current day's city get 1 extra credit.
#       - Otherwise, only the current day's city gets 1 credit.
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

# Helper: on day d, the itinerary "includes" a target city.
# If a flight occurs on day d, then both the departure (from day d-1) and arrival (day d) are counted.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Event constraints:
#    You must attend a conference in Mykonos on day 4 and day 9.
#    (Recall days are numbered from 1 to 9, so day 4 is index 3 and day 9 is index 8.)
s.add(inCityOnDay(3, 0))
s.add(inCityOnDay(8, 0))

# Solve the model and, if found, display the itinerary.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_info = f"Day {d+1:2d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[city_idx]
            day_info += f" (Flight: {dep} -> {arr})"
        print(day_info)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")