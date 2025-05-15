from z3 import *

# City indices and requirements:
# 0: Riga    – 5 days.
# 1: Vilnius – 7 days.
# 2: Dublin  – 2 days.
city_names = ["Riga", "Vilnius", "Dublin"]
req = [5, 7, 2]  # Total required day credits = 5 + 7 + 2 = 14

# Total base days = 12.
# On a day with no flight, you get 1 credit for the city.
# On a flight day (flying from A to B on day X) both A and B get a credit.
# Thus, total credits = 12 + (# flights).
# To achieve 14 credits, we need exactly 2 flights.
# This partitions the trip into 3 segments (one per city).
DAYS = 12

# Allowed direct flights:
# "Dublin and Riga" (bidirectional): (2,0) and (0,2)
# "from Riga to Vilnius" (unidirectional): (0,1)
allowed_flights = [
    (2,0), (0,2),
    (0,1)
]

# Create Z3 variables:
# c[d] is the base city on day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is True iff a flight occurs on day d (for d>=1; day 0 is starting day, so no flight).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a new segment (day 0 or a day with a flight).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain constraints: each day's city is in {0, 1, 2}.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 is always a segment start.
s.add(isSeg[0] == True)

# 3. For days d>=1, define flight occurrence and allowed transitions.
for d in range(1, DAYS):
    # A flight occurs if the city changes.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs, then the transition (c[d-1] -> c[d]) must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly 2 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 2)

# 5. Distinct segment constraint:
# The starting city for each segment (day 0 and each flight day) must be unique,
# ensuring that each city is visited exactly once.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))
# Also ensure that every city appears as a segment start.
for city in range(len(city_names)):
    s.add(Or([And(isSeg[d], c[d] == city) for d in range(DAYS)]))

# 6. Compute day contributions for each city:
# Day 0 gives a single credit for c[0].
# For each day d >= 1:
#  - If a flight occurs on day d, add credit to both c[d-1] and c[d].
#  - Otherwise, add credit to c[d] only.
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

# Solve the model and output the itinerary.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_string = f"Day {d+1:2d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[city_idx]
            day_string += f" (Flight: {dep} -> {arr})"
        print(day_string)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")