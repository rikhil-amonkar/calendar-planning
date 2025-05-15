from z3 import *

# We have 3 cities:
# 0: Venice   – 6 days; event: attend workshop between day 5 and day 10.
# 1: Mykonos  – 2 days.
# 2: Vienna   – 4 days.
city_names = ["Venice", "Mykonos", "Vienna"]
req = [6, 2, 4]  # Total contributions required = 6+2+4 = 12

# Total base days = 10. Each flight day gives an extra contribution.
# So total day credits = 10 + (# flights).
# To meet 12 credits, we need exactly 2 flights.
# With 2 flights, the itinerary is partitioned into 3 segments, one per city.
DAYS = 10

# Allowed direct flights:
# "Mykonos and Vienna" -> allowed in both directions: (1,2) and (2,1)
# "Vienna and Venice"   -> allowed in both directions: (2,0) and (0,2)
allowed_flights = [
    (1,2), (2,1),
    (2,0), (0,2)
]

# Create Z3 variables.
# c[d]: the "base" city on day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d]: True if a flight occurs on day d (for d >= 1; day 0 has no flight).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d]: True if day d is the start of a new city segment (i.e. day 0 or when a flight occurs).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain constraints: c[d] in {0, 1, 2} for each day.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 is always the start of a segment.
s.add(isSeg[0] == True)

# 3. For days d>=1, determine if a flight occurs and enforce allowed flight transitions.
for d in range(1, DAYS):
    # A flight occurs if the base city changes.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If there is a flight on day d, then the transition (c[d-1] -> c[d]) must be one of the allowed flights.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. We need exactly 2 flights.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 2)

# 5. The starting base city of each segment (day 0 and days with a flight) 
# must be distinct (ensuring that each city is visited exactly once).
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally, ensure every city is visited once.
for city in range(len(city_names)):
    s.add(Or([And(isSeg[d], c[d] == city) for d in range(DAYS)]))

# 6. Compute the day contributions for each city.
# Day 0 contributes 1 to c[0]. For each day d>=1:
#   - If a flight occurs on day d, both the previous (departure) and current (arrival) cities get +1.
#   - Otherwise, only the current city's count is incremented by 1.
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

# Helper function: on day d the itinerary "includes" a target city.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Event constraint: Attend a workshop in Venice (city 0) between day 5 and day 10.
# That is, in at least one day between indices 4 and 9.
workshop_event = [inCityOnDay(d, 0) for d in range(4, DAYS)]
s.add(Or(workshop_event))

# Solve the model and output the itinerary.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        line = f"Day {d+1:2d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            frm = city_names[m[c[d-1]].as_long()]
            to = city_names[city_idx]
            line += f" (Flight: {frm} -> {to})"
        print(line)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")