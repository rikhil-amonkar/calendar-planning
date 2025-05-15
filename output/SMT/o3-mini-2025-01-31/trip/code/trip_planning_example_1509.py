from z3 import *

# City indices and their requirements:
# 0: Paris      – 5 days; event: meet friends at Paris between day 4 and day 8.
# 1: Warsaw     – 2 days; event: also used in flight constraints.
# 2: Krakow     – 2 days; event: attend a workshop in Krakow between day 17 and day 18.
# 3: Tallinn    – 2 days.
# 4: Riga       – 2 days; event: attend a wedding in Riga between day 23 and day 24.
# 5: Copenhagen – 5 days.
# 6: Helsinki   – 5 days; event: meet a friend in Helsinki between day 18 and day 22.
# 7: Oslo       – 5 days.
# 8: Santorini  – 2 days; event: visit relatives in Santorini between day 12 and day 13.
# 9: Lyon       – 4 days.
city_names = ["Paris", "Warsaw", "Krakow", "Tallinn", "Riga", "Copenhagen", "Helsinki", "Oslo", "Santorini", "Lyon"]
req = [5, 2, 2, 2, 2, 5, 5, 5, 2, 4]  # Sum = 34

# Total base days:
DAYS = 25
# Each day without a flight gives 1 credit; when flying on a day, the departure and arrival both get a credit.
# So total credits = 25 + (# flights). We require total credits = 34.
# Hence, # flights must be 34 - 25 = 9.
# This divides the itinerary into 10 segments (one per city visited).

# Allowed direct flights. For each flight, we list ordered pairs (from, to).
allowed_flights = [
    # Warsaw and Riga
    (1, 4), (4, 1),
    # Warsaw and Tallinn
    (1, 3), (3, 1),
    # Copenhagen and Helsinki
    (5, 6), (6, 5),
    # Lyon and Paris
    (9, 0), (0, 9),
    # Copenhagen and Warsaw
    (5, 1), (1, 5),
    # Lyon and Oslo
    (9, 7), (7, 9),
    # Paris and Oslo
    (0, 7), (7, 0),
    # Paris and Riga
    (0, 4), (4, 0),
    # Krakow and Helsinki
    (2, 6), (6, 2),
    # Paris and Tallinn
    (0, 3), (3, 0),
    # Oslo and Riga
    (7, 4), (4, 7),
    # Krakow and Warsaw
    (2, 1), (1, 2),
    # Paris and Helsinki
    (0, 6), (6, 0),
    # Copenhagen and Santorini
    (5, 8), (8, 5),
    # Helsinki and Warsaw
    (6, 1), (1, 6),
    # Helsinki and Riga
    (6, 4), (4, 6),
    # Copenhagen and Riga
    (5, 4), (4, 5),
    # Paris and Krakow
    (0, 2), (2, 0),
    # Copenhagen and Oslo
    (5, 7), (7, 5),
    # Oslo and Tallinn
    (7, 3), (3, 7),
    # Oslo and Helsinki
    (7, 6), (6, 7),
    # Copenhagen and Tallinn
    (5, 3), (3, 5),
    # Oslo and Krakow
    (7, 2), (2, 7),
    # from Riga to Tallinn (unidirectional)
    (4, 3),
    # Helsinki and Tallinn (bidirectional)
    (6, 3), (3, 6),
    # Paris and Copenhagen
    (0, 5), (5, 0),
    # Paris and Warsaw
    (0, 1), (1, 0),
    # from Santorini to Oslo (unidirectional)
    (8, 7),
    # Oslo and Warsaw
    (7, 1), (1, 7)
]

# Create Z3 variables:
# c[d] is the base city on day d (0-indexed days)
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is True if a flight occurs on day d (for d>=1; day 0 is starting day with no flight)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a new segment (either day 0 or a day with a flight)
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain constraints: each day's city index is between 0 and 9.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 is always the start of a segment.
s.add(isSeg[0] == True)

# 3. For days d>=1 determine flight occurrence and enforce allowed transitions.
for d in range(1, DAYS):
    # Flight occurs if today's city differs from previous day's city.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs, then the transition (c[d-1] -> c[d]) must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly 9 flights must occur among days 1..(DAYS-1).
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 9)

# 5. Distinct Segment Constraint:
# The starting city of each segment (day 0 and any flight day) must be distinct.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))
# Also, enforce that every city appears as a segment start.
for city in range(len(city_names)):
    s.add(Or([And(isSeg[d], c[d] == city) for d in range(DAYS)]))

# 6. Compute day contributions for each city.
# Day 0 contributes 1 to city c[0].
# For every day d>=1:
#  - If a flight occurs on day d, add 1 credit for both c[d-1] and c[d].
#  - Otherwise, add 1 credit for c[d] only.
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
    # Enforce required day credits.
    s.add(counts[city] == req[city])

# Helper function to check if city 'target' is visited on day d.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Event Constraints:
# (a) Meet friends at Paris (city 0) between day 4 and day 8 (indices 3 to 7).
paris_event = [inCityOnDay(d, 0) for d in range(3, 8)]
s.add(Or(paris_event))

# (b) Workshop in Krakow (city 2) between day 17 and day 18 (indices 16 and 17).
krakow_workshop = [inCityOnDay(d, 2) for d in [16, 17]]
s.add(Or(krakow_workshop))

# (c) Wedding in Riga (city 4) between day 23 and day 24 (indices 22 and 23).
riga_wedding = [inCityOnDay(d, 4) for d in [22, 23]]
s.add(Or(riga_wedding))

# (d) Meet a friend in Helsinki (city 6) between day 18 and day 22 (indices 17 to 21).
helsinki_event = [inCityOnDay(d, 6) for d in range(17, 22)]
s.add(Or(helsinki_event))

# (e) Visit relatives in Santorini (city 8) between day 12 and day 13 (indices 11 and 12).
santorini_event = [inCityOnDay(d, 8) for d in [11, 12]]
s.add(Or(santorini_event))

# Solve the model and print the itinerary.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_out = f"Day {d+1:2d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[city_idx]
            day_out += f" (Flight: {dep} -> {arr})"
        print(day_out)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")