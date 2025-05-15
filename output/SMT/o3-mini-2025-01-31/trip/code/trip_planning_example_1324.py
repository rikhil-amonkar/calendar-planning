from z3 import *

# City indices and requirements:
# 0: Venice     – 4 days
# 1: Barcelona  – 3 days; event: meet a friend in Barcelona between day 10 and day 12.
# 2: Copenhagen – 4 days; event: visit relatives in Copenhagen between day 7 and day 10.
# 3: Lyon       – 4 days
# 4: Reykjavik  – 4 days
# 5: Dubrovnik  – 5 days; event: attend a wedding in Dubrovnik between day 16 and day 20.
# 6: Athens     – 2 days
# 7: Tallinn    – 5 days
# 8: Munich     – 3 days
city_names = ["Venice", "Barcelona", "Copenhagen", "Lyon", "Reykjavik", "Dubrovnik", "Athens", "Tallinn", "Munich"]
req = [4, 3, 4, 4, 4, 5, 2, 5, 3]  # Total = 34

# Base days = 26. Extra contributions come from flight days.
# Each flight day adds an extra contribution relative to a stay day.
# Therefore, extra needed = 34 - 26 = 8. Exactly 8 flight days are required.
# This partitions the trip into 9 segments (each segment representing one city visit).
DAYS = 26

# Allowed direct flights.
# Note: unless specified, flights are bidirectional. "from Reykjavik to Athens" is one-way.
allowed_flights = [
    # Copenhagen and Athens
    (2,6), (6,2),
    # Copenhagen and Dubrovnik
    (2,5), (5,2),
    # Munich and Tallinn
    (8,7), (7,8),
    # Copenhagen and Munich
    (2,8), (8,2),
    # Venice and Munich
    (0,8), (8,0),
    # from Reykjavik to Athens (one-way)
    (4,6),
    # Athens and Dubrovnik
    (6,5), (5,6),
    # Venice and Athens
    (0,6), (6,0),
    # Lyon and Barcelona
    (3,1), (1,3),
    # Copenhagen and Reykjavik
    (2,4), (4,2),
    # Reykjavik and Munich
    (4,8), (8,4),
    # Athens and Munich
    (6,8), (8,6),
    # Lyon and Munich
    (3,8), (8,3),
    # Barcelona and Reykjavik
    (1,4), (4,1),
    # Venice and Copenhagen
    (0,2), (2,0),
    # Barcelona and Dubrovnik
    (1,5), (5,1),
    # Lyon and Venice
    (3,0), (0,3),
    # Dubrovnik and Munich
    (5,8), (8,5),
    # Barcelona and Athens
    (1,6), (6,1),
    # Copenhagen and Barcelona
    (2,1), (1,2),
    # Venice and Barcelona
    (0,1), (1,0),
    # Barcelona and Munich
    (1,8), (8,1),
    # Barcelona and Tallinn
    (1,7), (7,1),
    # Copenhagen and Tallinn
    (2,7), (7,2)
]

# Create Z3 variables.
# c[d] is the base city on day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is True if a flight occurs on day d (d>=1; day0 is simply the start city)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a new segment (day 0 or when a flight occurs)
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain: Each c[d] must be an integer in [0, len(city_names)-1].
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 is always a segment start.
s.add(isSeg[0] == True)

# 3. For each day d>=1, determine if a flight occurs and enforce that if a flight does occur,
# then the (previous city -> current city) pair is among the allowed flights.
for d in range(1, DAYS):
    # Flight occurs if and only if the base city changes.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly 8 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 8)

# 5. The starting base city of each segment (day 0 and days with a flight)
# must all be distinct so that each city is visited exactly once.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally, ensure that every city is visited at least once.
for city in range(len(city_names)):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# 6. Calculate day contributions for each city.
# Day 0 contributes 1 to the city c[0].
# For each day d>=1:
#   - If a flight occurs on day d, then both c[d-1] (departure) and c[d] (arrival) get +1.
#   - Otherwise, only c[d] gets +1.
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

# Helper: Returns condition that on day d the itinerary "includes" target city.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Event constraints:
# (a) Meet a friend in Barcelona (city 1) between day 10 and day 12: days indices 9, 10, 11.
friend_event = [inCityOnDay(d, 1) for d in range(9, 12)]
s.add(Or(friend_event))

# (b) Visit relatives in Copenhagen (city 2) between day 7 and day 10: days indices 6, 7, 8, 9.
relatives_event = [inCityOnDay(d, 2) for d in range(6, 10)]
s.add(Or(relatives_event))

# (c) Attend a wedding in Dubrovnik (city 5) between day 16 and day 20: days indices 15, 16, 17, 18, 19.
wedding_event = [inCityOnDay(d, 5) for d in range(15, 20)]
s.add(Or(wedding_event))

# Solve and output the itinerary.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_str = f"Day {d+1:2d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep_city = city_names[m[c[d-1]].as_long()]
            arr_city = city_names[city_idx]
            day_str += f" (Flight: {dep_city} -> {arr_city})"
        print(day_str)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")