from z3 import *

# City mapping and requirements:
# 0: Stuttgart  – 5 days; event: attend a workshop in Stuttgart between day 11 and day 15.
# 1: Manchester – 7 days; event: attend a wedding in Manchester between day 1 and day 7.
# 2: Madrid     – 4 days.
# 3: Vienna     – 2 days.
city_names = ["Stuttgart", "Manchester", "Madrid", "Vienna"]
req = [5, 7, 4, 2]  # Total required day credits = 5+7+4+2 = 18

# Total base days = 15.
# On a day with no flight, you get 1 credit.
# On a flight day (if flying from A to B on that day) both cities get 1 credit.
# Total credits = 15 + (# flights)
# To reach 18 credits, we need exactly 3 flights.
# This partitions the trip into 4 segments (each segment corresponds to one city visit).
DAYS = 15

# Allowed direct flights (bidirectional unless noted differently):
# Vienna and Stuttgart:         (3,0) and (0,3)
# Manchester and Vienna:         (1,3) and (3,1)
# Madrid and Vienna:             (2,3) and (3,2)
# Manchester and Stuttgart:      (1,0) and (0,1)
# Manchester and Madrid:         (1,2) and (2,1)
allowed_flights = [
    (3,0), (0,3),
    (1,3), (3,1),
    (2,3), (3,2),
    (1,0), (0,1),
    (1,2), (2,1)
]

# Create Z3 variables:
# c[d] denotes the base city on day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is True if a flight happens on day d (for d>=1; day 0 never is a flight day).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a new segment (day 0 or when a flight occurs)
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain constraints: each day's city is in {0,1,2,3}.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 is always the start of a segment.
s.add(isSeg[0] == True)

# 3. For each day d>=1, determine if a flight occurs and restrict transitions.
for d in range(1, DAYS):
    # A flight occurs on day d if the city changes from day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight happens on day d, then transition (c[d-1] -> c[d]) must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly 3 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 3)

# 5. Distinct segment constraint:
# The starting base city of each segment (day 0 and flight days) must be distinct,
# which enforces that each city is visited exactly once.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))
# Also enforce each city appears as a segment start.
for city in range(len(city_names)):
    s.add(Or([And(isSeg[d], c[d] == city) for d in range(DAYS)]))

# 6. Compute day contributions for each city.
# Day 0 gives a credit for c[0].
# For each day d>=1:
#   - If flying on day d, both the previous day's city and the current city's day get a credit.
#   - Otherwise, only the current city's day gets a credit.
counts = [Int(f"count_{i}") for i in range(len(city_names))]
for city in range(len(city_names)):
    base = If(c[0] == city, 1, 0)
    daily = []
    for d in range(1, DAYS):
        daily.append(
            If(flight[d],
               # Flight day: credit goes to both c[d-1] and c[d]
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               # No flight: credit goes only to c[d]
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == base + Sum(daily))
    s.add(counts[city] == req[city])

# Helper: determine if on day d the itinerary includes the target city.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Event constraints:
# (a) Attend a wedding in Manchester (city 1) between day 1 and day 7 (indices 0 to 6)
wedding_event = [inCityOnDay(d, 1) for d in range(0, 7)]
s.add(Or(wedding_event))

# (b) Attend a workshop in Stuttgart (city 0) between day 11 and day 15 (indices 10 to 14)
workshop_event = [inCityOnDay(d, 0) for d in range(10, 15)]
s.add(Or(workshop_event))

# Solve the model and print the itinerary.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        out = f"Day {d+1:2d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[city_idx]
            out += f" (Flight: {dep} -> {arr})"
        print(out)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")