from z3 import *

# Cities (indices and requirements):
# 0: Istanbul   – 4 days
# 1: Vienna     – 4 days
# 2: Riga       – 2 days
# 3: Brussels   – 2 days; event: wedding in Brussels between day 26 and day 27.
# 4: Madrid     – 4 days
# 5: Vilnius    – 4 days; event: meet friends at Vilnius between day 20 and day 23.
# 6: Venice     – 5 days; event: workshop in Venice between day 7 and day 11.
# 7: Geneva     – 4 days; event: visit relatives in Geneva between day 1 and day 4.
# 8: Munich     – 5 days
# 9: Reykjavik  – 2 days
city_names = ["Istanbul", "Vienna", "Riga", "Brussels", "Madrid", "Vilnius", "Venice", "Geneva", "Munich", "Reykjavik"]
req = [4, 4, 2, 2, 4, 4, 5, 4, 5, 2]

# Total required contributions = 4+4+2+2+4+4+5+4+5+2 = 36.
# Base days = 27, so extra contributions from flights = 36 - 27 = 9 flights.
# This partitions the itinerary into 10 segments (one per city).

DAYS = 27  # Days indices: 0..26 represent days 1..27

# Allowed direct flights:
# We'll list each pair as a tuple (from, to). For bidirectional connections, both orders are added.
allowed_flights = [
    # 1. Munich and Vienna
    (8,1), (1,8),
    # 2. Istanbul and Brussels
    (0,3), (3,0),
    # 3. Vienna and Vilnius
    (1,5), (5,1),
    # 4. Madrid and Munich
    (4,8), (8,4),
    # 5. Venice and Brussels
    (6,3), (3,6),
    # 6. Riga and Brussels
    (2,3), (3,2),
    # 7. Geneva and Istanbul
    (7,0), (0,7),
    # 8. Munich and Reykjavik
    (8,9), (9,8),
    # 9. Vienna and Istanbul
    (1,0), (0,1),
    # 10. Riga and Istanbul
    (2,0), (0,2),
    # 11. Reykjavik and Vienna
    (9,1), (1,9),
    # 12. Venice and Munich
    (6,8), (8,6),
    # 13. Madrid and Venice
    (4,6), (6,4),
    # 14. Vilnius and Istanbul
    (5,0), (0,5),
    # 15. Venice and Vienna
    (6,1), (1,6),
    # 16. Venice and Istanbul
    (6,0), (0,6),
    # 17. from Reykjavik to Madrid (one-way)
    (9,4),
    # 18. from Riga to Munich (one-way)
    (2,8),
    # 19. Munich and Istanbul
    (8,0), (0,8),
    # 20. Reykjavik and Brussels
    (9,3), (3,9),
    # 21. Vilnius and Brussels
    (5,3), (3,5),
    # 22. from Vilnius to Munich (one-way)
    (5,8),
    # 23. Madrid and Vienna
    (4,1), (1,4),
    # 24. Vienna and Riga
    (1,2), (2,1),
    # 25. Geneva and Vienna
    (7,1), (1,7),
    # 26. Madrid and Brussels
    (4,3), (3,4),
    # 27. Vienna and Brussels
    (1,3), (3,1),
    # 28. Geneva and Brussels
    (7,3), (3,7),
    # 29. Geneva and Madrid
    (7,4), (4,7),
    # 30. Munich and Brussels
    (8,3), (3,8),
    # 31. Madrid and Istanbul
    (4,0), (0,4),
    # 32. Geneva and Munich
    (7,8), (8,7),
    # 33. from Riga to Vilnius (one-way)
    (2,5)
]

# Create Z3 variables:
# c[d] : the base city on day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] : Boolean variable, True if a flight occurs on day d (for d >= 1).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] : indicates if day d is the start of a new segment (day 0 and when a flight occurs).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain Constraint: Each day's city must be one of 0..9.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 is always a segment start.
s.add(isSeg[0] == True)

# 3. For each day (from 1 to 26), determine if a flight occurs.
for d in range(1, DAYS):
    # A flight occurs if the city changes between days.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs on day d, the pair (c[d-1], c[d]) must be an allowed flight.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly 9 flights are required.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 9)

# 5. The starting city of each segment should be unique (so each city is visited exactly once).
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally, enforce that every city appears somewhere in the itinerary.
for city in range(len(city_names)):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# 6. Compute day contributions for each city.
# The model: day 0 contributes 1 to its city.
# For day d >= 1:
#   - If a flight occurs, then add 1 for the departure (c[d-1]) and 1 for the arrival (c[d]).
#   - Otherwise, add 1 for the city's day.
counts = [Int(f"count_{city}") for city in range(len(city_names))]
for city in range(len(city_names)):
    initial = If(c[0] == city, 1, 0)
    daily = []
    for d in range(1, DAYS):
        daily.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == initial + Sum(daily))
    s.add(counts[city] == req[city])

# Helper function: inCityOnDay
# Returns: a Z3 condition that day d "includes" being in target city.
# On a flight day, both the departure and arrival count.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Event Constraints:
# (a) Visit relatives in Geneva (city 7) between day 1 and day 4 -> indices 0..3.
geneva_event = [inCityOnDay(d, 7) for d in range(0, 4)]
s.add(Or(geneva_event))

# (b) Attend a workshop in Venice (city 6) between day 7 and day 11 -> indices 6..10.
venice_event = [inCityOnDay(d, 6) for d in range(6, 11)]
s.add(Or(venice_event))

# (c) Meet friends at Vilnius (city 5) between day 20 and day 23 -> indices 19..22.
vilnius_event = [inCityOnDay(d, 5) for d in range(19, 23)]
s.add(Or(vilnius_event))

# (d) Attend a wedding in Brussels (city 3) between day 26 and day 27 -> indices 25 and 26.
brussels_event = [inCityOnDay(d, 3) for d in [25, 26]]
s.add(Or(brussels_event))

# Solve and print the itinerary:
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_line = f"Day {d+1:2d}: {city_names[city_idx]}"
        # If a flight is taken on day d, include flight details.
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[city_idx]
            day_line += f" (Flight: {dep} -> {arr})"
        print(day_line)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")