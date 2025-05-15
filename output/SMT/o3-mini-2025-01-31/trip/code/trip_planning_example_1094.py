from z3 import *

# City indices and names:
# 0: Vienna      (4 days)
# 1: Barcelona   (2 days)
# 2: Edinburgh   (4 days) [event: meet friend in Edinburgh between day 12 and day 15]
# 3: Krakow      (3 days)
# 4: Riga        (4 days)
# 5: Hamburg     (2 days) [event: attend conference in Hamburg during day 10 and day 11]
# 6: Paris       (2 days) [event: attend wedding in Paris between day 1 and day 2]
# 7: Stockholm   (2 days) [event: visit relatives in Stockholm between day 15 and day 16]
city_names = ["Vienna", "Barcelona", "Edinburgh", "Krakow", "Riga", "Hamburg", "Paris", "Stockholm"]

# Required days per city:
req = [4, 2, 4, 3, 4, 2, 2, 2]
# Total required contributions = 4+2+4+3+4+2+2+2 = 23.
# Total base days = 16.
# Each flight day (when a flight occurs) contributes an extra count since that day counts for both departure and arrival.
# So we have: 16 + (#flights) = 23, which implies #flights = 7.
# With 7 flights, the itinerary is partitioned into 8 segments (each segment representing one visited city).

# Allowed direct flights (most are bidirectional; "from Riga to Hamburg" is one-way):
#  1. Hamburg and Stockholm: (5,7), (7,5)
#  2. Vienna and Stockholm: (0,7), (7,0)
#  3. Paris and Edinburgh: (6,2), (2,6)
#  4. Riga and Barcelona: (4,1), (1,4)
#  5. Paris and Riga: (6,4), (4,6)
#  6. Krakow and Barcelona: (3,1), (1,3)
#  7. Edinburgh and Stockholm: (2,7), (7,2)
#  8. Paris and Krakow: (6,3), (3,6)
#  9. Krakow and Stockholm: (3,7), (7,3)
# 10. Riga and Edinburgh: (4,2), (2,4)
# 11. Barcelona and Stockholm: (1,7), (7,1)
# 12. Paris and Stockholm: (6,7), (7,6)
# 13. Krakow and Edinburgh: (3,2), (2,3)
# 14. Vienna and Hamburg: (0,5), (5,0)
# 15. Paris and Hamburg: (6,5), (5,6)
# 16. Riga and Stockholm: (4,7), (7,4)
# 17. Hamburg and Barcelona: (5,1), (1,5)
# 18. Vienna and Barcelona: (0,1), (1,0)
# 19. Krakow and Vienna: (3,0), (0,3)
# 20. from Riga to Hamburg (one-way): (4,5)
# 21. Barcelona and Edinburgh: (1,2), (2,1)
# 22. Paris and Barcelona: (6,1), (1,6)
# 23. Hamburg and Edinburgh: (5,2), (2,5)
# 24. Paris and Vienna: (6,0), (0,6)
# 25. Vienna and Riga: (0,4), (4,0)
allowed_flights = [
    (5,7), (7,5),
    (0,7), (7,0),
    (6,2), (2,6),
    (4,1), (1,4),
    (6,4), (4,6),
    (3,1), (1,3),
    (2,7), (7,2),
    (6,3), (3,6),
    (3,7), (7,3),
    (4,2), (2,4),
    (1,7), (7,1),
    (6,7), (7,6),
    (3,2), (2,3),
    (0,5), (5,0),
    (6,5), (5,6),
    (4,7), (7,4),
    (5,1), (1,5),
    (0,1), (1,0),
    (3,0), (0,3),
    (4,5),   # from Riga to Hamburg (one-way)
    (1,2), (2,1),
    (6,1), (1,6),
    (5,2), (2,5),
    (6,0), (0,6),
    (0,4), (4,0)
]

# Total base days in the itinerary.
DAYS = 16

# Create Z3 variables.
# c[d] is the base city on day d (with d from 0 to 15, corresponding to days 1 to 16).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] indicates if a flight happens on day d (for d >= 1).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] indicates that day d is the start of a new segment (day 0 is always a segment start).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Ensure every day's base city is within the valid range 0..7.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < 8)

# Day 0 is the beginning of a segment.
s.add(isSeg[0] == True)

# Define flight conditions for days 1 to DAYS-1.
for d in range(1, DAYS):
    # A flight occurs on day d if the city changes from the previous day.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs, the route must be in the allowed flights list.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Exactly 7 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 7)

# Ensure that the starting city of every segment (day 0 and any day d with a flight)
# is distinct, so that each visited city is unique.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally enforce that every city is visited at least once.
for city in range(8):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Calculate day contributions for each city.
# Day 0 contributes 1 to c[0]. For each day d from 1 to 15:
#   - If a flight occurs, day d contributes 1 to both the departure (c[d-1]) and arrival (c[d]).
#   - Otherwise, it contributes 1 to the city c[d] only.
counts = [Int(f"count_{i}") for i in range(8)]
for i in range(8):
    init = If(c[0] == i, 1, 0)
    daily = []
    for d in range(1, DAYS):
        daily.append(
            If(flight[d],
               If(c[d-1] == i, 1, 0) + If(c[d] == i, 1, 0),
               If(c[d] == i, 1, 0)
            )
        )
    s.add(counts[i] == init + Sum(daily))
    s.add(counts[i] == req[i])

# Helper function: inCityOnDay(d, target)
# Returns a condition that on day d, the itinerary "includes" the target city.
# In case a flight happens on day d, both the departure and arrival cities are considered.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Event constraints:

# 1. Wedding in Paris (city 6) between day 1 and day 2.
#    That covers day 1 and day 2 (indices 0 and 1).
wedding_paris = [inCityOnDay(d, 6) for d in [0, 1]]
s.add(Or(wedding_paris))

# 2. Conference in Hamburg (city 5) during day 10 and day 11.
#    That covers day 10 and day 11, i.e. indices 9 and 10.
conference_hamburg = [inCityOnDay(d, 5) for d in [9, 10]]
s.add(Or(conference_hamburg))

# 3. Meet a friend in Edinburgh (city 2) between day 12 and day 15.
#    That covers days 12, 13, 14, 15 (indices 11,12,13,14).
meet_friend = [inCityOnDay(d, 2) for d in range(11, 15)]
s.add(Or(meet_friend))

# 4. Visit relatives in Stockholm (city 7) between day 15 and day 16.
#    That covers day 15 and day 16 (indices 14 and 15).
relatives_stockholm = [inCityOnDay(d, 7) for d in [14, 15]]
s.add(Or(relatives_stockholm))

# Check for a solution.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        base = m[c[d]].as_long()
        day_info = f"Day {d+1:2d}: {city_names[base]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[base]
            day_info += f" (Flight: {dep} -> {arr})"
        print(day_info)
    print("\nCity day counts:")
    for i in range(8):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")