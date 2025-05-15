from z3 import *

# City indices and requirements:
# 0: Brussels  – 5 days; event: workshop in Brussels between day 7 and day 11.
# 1: Rome      – 2 days
# 2: Dubrovnik – 3 days
# 3: Geneva    – 5 days
# 4: Budapest  – 2 days; event: meet friend in Budapest between day 16 and day 17.
# 5: Riga      – 4 days; event: meet friends at Riga between day 4 and day 7.
# 6: Valencia  – 2 days
city_names = ["Brussels", "Rome", "Dubrovnik", "Geneva", "Budapest", "Riga", "Valencia"]
req = [5, 2, 3, 5, 2, 4, 2]  # required day contributions

# Total required day contributions = 5+2+3+5+2+4+2 = 23.
# With 17 base days, extra contributions come from flights.
# 23 - 17 = 6, so exactly 6 flights are required, partitioning the itinerary into 7 segments.

DAYS = 17  # Days indices 0..16 represent days 1..17

# Allowed direct flights (each tuple is (from, to)):
# Brussels and Valencia:        (0,6) and (6,0)
# Rome and Valencia:            (1,6) and (6,1)
# Brussels and Geneva:          (0,3) and (3,0)
# Rome and Geneva:              (1,3) and (3,1)
# Dubrovnik and Geneva:         (2,3) and (3,2)
# Valencia and Geneva:          (6,3) and (3,6)
# from Rome to Riga:            (1,5)  [one-way]
# Geneva and Budapest:          (3,4) and (4,3)
# Riga and Brussels:            (5,0) and (0,5)
# Rome and Budapest:            (1,4) and (4,1)
# Rome and Brussels:            (1,0) and (0,1)
# Brussels and Budapest:        (0,4) and (4,0)
# Dubrovnik and Rome:           (2,1) and (1,2)
allowed_flights = [
    (0,6), (6,0),
    (1,6), (6,1),
    (0,3), (3,0),
    (1,3), (3,1),
    (2,3), (3,2),
    (6,3), (3,6),
    (1,5),  # one-way: from Rome to Riga
    (3,4), (4,3),
    (5,0), (0,5),
    (1,4), (4,1),
    (0,4), (4,0),
    (2,1), (1,2)
]

# Create Z3 variables:
# c[d] represents the "base" city on day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] indicates if a flight is taken on day d (for d>=1)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d starts a new segment (day 0 and every flight day)
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain: each day's city must be one of the cities (indices 0..6)
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 is always a segment start.
s.add(isSeg[0] == True)

# 3. For days 1 through 16, determine if a flight happens.
for d in range(1, DAYS):
    # A flight occurs if the city changes from the previous day.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs, then (c[d-1], c[d]) must be one of the allowed direct flights.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly 6 flights are required.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 6)

# 5. The starting city of each segment (day 0 and flight days) should be unique.
for i in range(DAYS):
    for j in range(i + 1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally, ensure every city is visited.
for city in range(len(city_names)):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# 6. Compute day contributions for each city.
# On day 0, the city c[0] gets 1 day.
# For day d (d>=1):
#   - If a flight occurs on day d, then both c[d-1] and c[d] are credited.
#   - If no flight occurs then only c[d] is credited.
counts = [Int(f"count_{city}") for city in range(len(city_names))]
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

# Helper function: inCityOnDay(d, target)
# Returns a condition asserting that on day d, the itinerary "includes" the target city.
# On a flight day, either the departure (c[d-1]) or the arrival (c[d]) qualifies.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Event constraints:
# (a) Workshop in Brussels (city 0) between day 7 and day 11.
#     That is, for some day in indices 6 to 10, the itinerary must include Brussels.
workshop_event = [inCityOnDay(d, 0) for d in range(6, 11)]
s.add(Or(workshop_event))

# (b) Meeting friends at Riga (city 5) between day 4 and day 7.
#     That is, for some day in indices 3,4,5,6, the itinerary must include Riga.
riga_event = [inCityOnDay(d, 5) for d in [3, 4, 5, 6]]
s.add(Or(riga_event))

# (c) Meet a friend in Budapest (city 4) between day 16 and day 17.
#     That is, for some day in indices 15 or 16, the itinerary must include Budapest.
budapest_event = [inCityOnDay(d, 4) for d in [15, 16]]
s.add(Or(budapest_event))

# Solve and print the itinerary:
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
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")