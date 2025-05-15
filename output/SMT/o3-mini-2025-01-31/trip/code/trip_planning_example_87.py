from z3 import *

# City indices and requirements:
# 0: Riga     – 2 days; event: visit relatives in Riga between day 1 and day 2.
# 1: Amsterdam– 2 days
# 2: Mykonos  – 5 days
city_names = ["Riga", "Amsterdam", "Mykonos"]
req = [2, 2, 5]

# Total required day contributions = 2 + 2 + 5 = 9.
# Base days = 7, so extra contributions = 9 - 7 = 2.
# Each flight day (when a flight occurs) contributes an extra day.
# Therefore, exactly 2 flights must be taken.
# This partitions the itinerary into 3 segments, so each city is visited once.

DAYS = 7  # Days are indexed 0 to 6 (i.e., day1 to day7)

# Allowed direct flights (bidirectional unless otherwise stated):
# Amsterdam and Mykonos
# Riga and Amsterdam
allowed_flights = [
    (1,2), (2,1),   # Amsterdam <-> Mykonos
    (0,1), (1,0)    # Riga <-> Amsterdam
]

# Create Z3 variables:
# c[d] represents the city on day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] indicates if a flight occurs on day d (for d >= 1)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a new segment (i.e., day 0 or a day when a flight occurs)
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain: The city index on each day is in {0, 1, 2}.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 is always the start of a segment.
s.add(isSeg[0] == True)

# 3. Determine flight occurrence and enforce allowed flights.
for d in range(1, DAYS):
    # A flight occurs if the city changes (i.e., c[d] != c[d-1]).
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs on day d, then (c[d-1] -> c[d]) must be an allowed flight.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly 2 flights must take place.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 2)

# 5. The starting city of each segment (day 0 and each day with a flight) must be unique.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally, enforce that every city is visited at least once.
for city in range(len(city_names)):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# 6. Calculate day contributions for each city.
# Day 0 contributes 1 for city c[0].
# For each day d >= 1:
#   - If a flight takes place, both c[d-1] and c[d] get +1 each.
#   - Otherwise, only c[d] gets +1.
counts = [Int(f"count_{i}") for i in range(len(city_names))]
for city in range(len(city_names)):
    base = If(c[0] == city, 1, 0)
    daily_sum = []
    for d in range(1, DAYS):
        daily_sum.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == base + Sum(daily_sum))
    s.add(counts[city] == req[city])

# 7. Event constraint: visit relatives in Riga (city 0) between day 1 and day 2.
# That is, on at least one of day 1 or day 2 (indices 0 or 1) the itinerary should include Riga.
# Note: For day 1 (index 0) it's just c[0]; for day 2 (index 1) if a flight happens, then it includes both c[0] and c[1].
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

relatives_event = [inCityOnDay(d, 0) for d in [0, 1]]
s.add(Or(relatives_event))

# Solve the constraints and print the itinerary.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_str = f"Day {d+1:2d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            from_city = city_names[m[c[d-1]].as_long()]
            to_city = city_names[city_idx]
            day_str += f" (Flight: {from_city} -> {to_city})"
        print(day_str)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")