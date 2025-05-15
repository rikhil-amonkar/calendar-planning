from z3 import *

# City indices and requirements:
# 0: Lyon       – 7 days
# 1: Bucharest  – 7 days; event: attend a wedding in Bucharest between day 1 and day 7.
# 2: Porto      – 4 days
city_names = ["Lyon", "Bucharest", "Porto"]
req = [7, 7, 4]  # Total = 7 + 7 + 4 = 18

# Base days = 16. Extra contributions come from flight days. 
# Since each flight day adds one extra contribution, we require exactly 18 - 16 = 2 flights.
# This means the trip is partitioned into 3 segments (each segment corresponds to one visited city).

DAYS = 16  # Days indices: 0 through 15 (i.e., day 1 to day 16)

# Allowed direct flights (bidirectional):
# "Bucharest and Lyon" implies (Bucharest, Lyon) and (Lyon, Bucharest)
# "Lyon and Porto" implies (Lyon, Porto) and (Porto, Lyon)
allowed_flights = [
    (1, 0), (0, 1),
    (0, 2), (2, 0)
]

# Create Z3 variables.
# c[d]: the "base" city on day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d]: Boolean variable indicating whether a flight occurs on day d (d >= 1)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d]: Boolean indicating that day d is the start of a new segment (day 0 or a day with a flight)
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain constraints: Each day's base city is one of {0, 1, 2}.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 is always a segment start.
s.add(isSeg[0] == True)

# 3. Determine flight occurrence between consecutive days and enforce allowed flights.
for d in range(1, DAYS):
    # A flight occurs if the city on day d is different from day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If there is a flight on day d, then the transition (c[d-1] -> c[d]) must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly 2 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 2)

# 5. The starting base cities of each segment (day 0 and any day with a flight) must be unique.
# This ensures that each city is visited exactly once.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally ensure that every city is visited.
for city in range(len(city_names)):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# 6. Compute the day contributions for each city.
# Day 0 contributes 1 for city c[0].
# For each day d >= 1:
#   - if a flight occurs on day d, then both the departure (c[d-1]) and the arrival (c[d]) get +1
#   - if no flight occurs, then c[d] gets +1.
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

# Helper function: inCityOnDay(d, target)
# On day d, if a flight occurs then both the departure and the arrival cities
# are considered "present" on day d; otherwise, only the base city c[d] is.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Event constraint: Attend a wedding in Bucharest (city 1) between day 1 and day 7.
# That is, for at least one of days 1 to 7 (indices 0 to 6), the itinerary must include Bucharest.
wedding_event = [inCityOnDay(d, 1) for d in range(0, 7)]
s.add(Or(wedding_event))

# Solve the model and output the itinerary.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_output = f"Day {d+1:2d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[city_idx]
            day_output += f" (Flight: {dep} -> {arr})"
        print(day_output)
    
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")