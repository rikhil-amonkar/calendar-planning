from z3 import *

# City indices and names:
# 0: Porto       (2 days)
# 1: Geneva      (3 days)
# 2: Mykonos     (3 days; event: meet a friend in Mykonos between day 10 and day 12)
# 3: Manchester  (4 days; event: attend a wedding in Manchester between day 15 and day 18)
# 4: Hamburg     (5 days)
# 5: Naples      (5 days)
# 6: Frankfurt   (2 days; event: annual show in Frankfurt from day 5 to day 6)
city_names = ["Porto", "Geneva", "Mykonos", "Manchester", "Hamburg", "Naples", "Frankfurt"]

# Required day contributions for each city:
# Sum = 2 + 3 + 3 + 4 + 5 + 5 + 2 = 24.
req = [2, 3, 3, 4, 5, 5, 2]

# We plan for 18 base days.
# Each flight day counts twice (departure and arrival).
# So total contributions = base_days + (#flights) which must equal 24.
# => 18 + (#flights) = 24  ->  #flights = 6.
# This partitions the itinerary into 7 segments (one for each visited city).

# Allowed direct flights (most bidirectional, except "from Hamburg to Geneva" is one-way):
allowed_flights = [
    # Hamburg and Frankfurt
    (4,6), (6,4),
    # Naples and Mykonos
    (5,2), (2,5),
    # Hamburg and Porto
    (4,0), (0,4),
    # from Hamburg to Geneva (one-way)
    (4,1),
    # Mykonos and Geneva
    (2,1), (1,2),
    # Frankfurt and Geneva
    (6,1), (1,6),
    # Frankfurt and Porto
    (6,0), (0,6),
    # Geneva and Porto
    (1,0), (0,1),
    # Geneva and Manchester
    (1,3), (3,1),
    # Naples and Manchester
    (5,3), (3,5),
    # Frankfurt and Naples
    (6,5), (5,6),
    # Frankfurt and Manchester
    (6,3), (3,6),
    # Naples and Geneva
    (5,1), (1,5),
    # Porto and Manchester
    (0,3), (3,0),
    # Hamburg and Manchester
    (4,3), (3,4)
]

DAYS = 18  # Base days

# Create Z3 variables:
# c[d] is the base city on day d (0-indexed: day d corresponds to day d+1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] indicates if a flight occurs on day d (for d>=1)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a new segment (day 0 always starts a segment)
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Each day's base city must be in 0..6.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < 7)

# Day 0 starts a segment.
s.add(isSeg[0] == True)

# For days 1 to 17:
for d in range(1, DAYS):
    # A flight occurs on day d if the city changes from day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs, the flight from c[d-1] to c[d] must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Exactly 6 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 6)

# Ensure the starting city of each segment (day 0 and any day with a flight) is distinct.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally enforce that every city is visited at least once.
for city in range(7):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Compute day contributions for each city.
# - Day 0 contributes 1 to the city c[0].
# - For day d from 1 to DAYS-1:
#     if a flight occurs, day d contributes 1 to both c[d-1] and c[d];
#     if no flight, it contributes 1 to c[d] only.
counts = [Int(f"count_{city}") for city in range(7)]
for city in range(7):
    init = If(c[0] == city, 1, 0)
    daily_sum = []
    for d in range(1, DAYS):
        daily_sum.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == init + Sum(daily_sum))
    s.add(counts[city] == req[city])

# Helper function: Generates constraint that day d "includes" target city.
# If a flight occurs on day d, then both the departure (c[d-1]) and arrival (c[d]) count.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Event constraints:

# 1. Meet a friend in Mykonos (city 2) between day 10 and day 12.
#    Days 10 to 12 correspond to indices 9, 10, and 11.
meet_friend_mykonos = [inCityOnDay(d, 2) for d in [9, 10, 11]]
s.add(Or(meet_friend_mykonos))

# 2. Attend a wedding in Manchester (city 3) between day 15 and day 18.
#    Days 15 to 18 correspond to indices 14, 15, 16, and 17.
wedding_manchester = [inCityOnDay(d, 3) for d in [14, 15, 16, 17]]
s.add(Or(wedding_manchester))

# 3. Annual show in Frankfurt (city 6) from day 5 to day 6.
#    Days 5 and 6 correspond to indices 4 and 5.
annual_show_frankfurt = [inCityOnDay(d, 6) for d in [4, 5]]
s.add(Or(annual_show_frankfurt))

# Check for a solution.
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
    print("\nCity day counts:")
    for i in range(7):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")