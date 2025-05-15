from z3 import *

# City indices and requirements:
# 0: Bucharest  – 2 days
# 1: Krakow     – 4 days
# 2: Munich     – 3 days; event: workshop in Munich between day 18 and day 20.
# 3: Barcelona  – 5 days
# 4: Warsaw     – 5 days; event: conference in Warsaw between day 25 and day 29.
# 5: Budapest   – 5 days; event: annual show in Budapest between day 9 and day 13.
# 6: Stockholm  – 2 days; event: meet friends at Stockholm between day 17 and day 18.
# 7: Riga       – 5 days
# 8: Edinburgh  – 5 days; event: meet friend in Edinburgh between day 1 and day 5.
# 9: Vienna     – 5 days
city_names = ["Bucharest", "Krakow", "Munich", "Barcelona", "Warsaw", "Budapest", "Stockholm", "Riga", "Edinburgh", "Vienna"]
req = [2, 4, 3, 5, 5, 5, 2, 5, 5, 5]

# Total required day contributions = 2+4+3+5+5+5+2+5+5+5 = 41.
# Base days = 32, so extra contributions = 41 - 32 = 9.
# Hence exactly 9 flights are needed, partitioning the trip into 10 segments.
DAYS = 32  # Day indices 0..31 represent days 1..32

# Allowed direct flights (using city indices):
allowed_flights = [
    # 1. Budapest and Munich
    (5,2), (2,5),
    # 2. Bucharest and Riga
    (0,7), (7,0),
    # 3. Munich and Krakow
    (2,1), (1,2),
    # 4. Munich and Warsaw
    (2,4), (4,2),
    # 5. Munich and Bucharest
    (2,0), (0,2),
    # 6. Edinburgh and Stockholm
    (8,6), (6,8),
    # 7. Barcelona and Warsaw
    (3,4), (4,3),
    # 8. Edinburgh and Krakow
    (8,1), (1,8),
    # 9. Barcelona and Munich
    (3,2), (2,3),
    # 10. Stockholm and Krakow
    (6,1), (1,6),
    # 11. Budapest and Vienna
    (5,9), (9,5),
    # 12. Barcelona and Stockholm
    (3,6), (6,3),
    # 13. Stockholm and Munich
    (6,2), (2,6),
    # 14. Edinburgh and Budapest
    (8,5), (5,8),
    # 15. Barcelona and Riga
    (3,7), (7,3),
    # 16. Edinburgh and Barcelona
    (8,3), (3,8),
    # 17. Vienna and Riga
    (9,7), (7,9),
    # 18. Barcelona and Budapest
    (3,5), (5,3),
    # 19. Bucharest and Warsaw
    (0,4), (4,0),
    # 20. Vienna and Krakow
    (9,1), (1,9),
    # 21. Edinburgh and Munich
    (8,2), (2,8),
    # 22. Barcelona and Bucharest
    (3,0), (0,3),
    # 23. Edinburgh and Riga
    (8,7), (7,8),
    # 24. Vienna and Stockholm
    (9,6), (6,9),
    # 25. Warsaw and Krakow
    (4,1), (1,4),
    # 26. Barcelona and Krakow
    (3,1), (1,3),
    # 27. from Riga to Munich (one-way)
    (7,2),
    # 28. Vienna and Bucharest
    (9,0), (0,9),
    # 29. Budapest and Warsaw
    (5,4), (4,5),
    # 30. Vienna and Warsaw
    (9,4), (4,9),
    # 31. Barcelona and Vienna
    (3,9), (9,3),
    # 32. Budapest and Bucharest
    (5,0), (0,5),
    # 33. Vienna and Munich
    (9,2), (2,9),
    # 34. Riga and Warsaw
    (7,4), (4,7),
    # 35. Stockholm and Riga
    (6,7), (7,6),
    # 36. Stockholm and Warsaw
    (6,4), (4,6)
]

# Create Z3 variables:
# c[d]: base city on day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d]: True if a flight occurs on day d (d>=1; day 0 is the start without a flight)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d]: True if day d is the start of a new segment (either day 0 or a flight day)
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain constraints: each c[d] must be one of the city indices.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 is the start of a segment.
s.add(isSeg[0] == True)

# 3. For each day d>=1, determine if a flight occurs and if so, enforce allowed flight.
for d in range(1, DAYS):
    # A flight happens if c[d] differs from c[d-1]
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If there's a flight, then (c[d-1], c[d]) must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly 9 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 9)

# 5. The starting city of each segment (day 0 and any flight day) must be unique.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally, enforce that every city is visited at least once.
for city in range(len(city_names)):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# 6. Compute day contributions for each city.
# Day 0 contributes 1 to the city c[0]. For each subsequent day:
# If a flight occurs on day d, then add 1 for both c[d-1] and c[d].
# If no flight, then add 1 for c[d].
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

# Helper function to indicate if on day d the itinerary "includes" a target city.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Event constraints:
# (a) Workshop in Munich (city 2) between day 18 and day 20 => indices 17,18,19.
workshop_munich = [inCityOnDay(d, 2) for d in range(17, 20)]
s.add(Or(workshop_munich))

# (b) Conference in Warsaw (city 4) between day 25 and day 29 => indices 24,25,26,27,28.
conference_warsaw = [inCityOnDay(d, 4) for d in range(24, 29)]
s.add(Or(conference_warsaw))

# (c) Annual show in Budapest (city 5) between day 9 and day 13 => indices 8,9,10,11,12.
annual_show = [inCityOnDay(d, 5) for d in range(8, 13)]
s.add(Or(annual_show))

# (d) Meet friends at Stockholm (city 6) between day 17 and day 18 => indices 16 and 17.
stockholm_meet = [inCityOnDay(d, 6) for d in [16, 17]]
s.add(Or(stockholm_meet))

# (e) Meet friend in Edinburgh (city 8) between day 1 and day 5 => indices 0,1,2,3,4.
edinburgh_meet = [inCityOnDay(d, 8) for d in range(0, 5)]
s.add(Or(edinburgh_meet))

# Solve and output the itinerary.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        line = f"Day {d+1:2d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[city_idx]
            line += f" (Flight: {dep} -> {arr})"
        print(line)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")