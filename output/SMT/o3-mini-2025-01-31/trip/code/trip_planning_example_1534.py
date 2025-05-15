from z3 import *

# City indices and names (in the order given):
# 0: Warsaw    (4 days)
# 1: Venice    (3 days)
# 2: Vilnius   (3 days)
# 3: Salzburg  (4 days; event: wedding in Salzburg between day 22 and day 25)
# 4: Amsterdam (2 days)
# 5: Barcelona (5 days; event: meet friends at Barcelona between day 2 and day 6)
# 6: Paris     (2 days; event: workshop in Paris between day 1 and day 2)
# 7: Hamburg   (4 days; event: conference in Hamburg during day 19 and day 22)
# 8: Florence  (5 days)
# 9: Tallinn   (2 days; event: meet a friend in Tallinn between day 11 and day 12)
city_names = ["Warsaw", "Venice", "Vilnius", "Salzburg", "Amsterdam",
              "Barcelona", "Paris", "Hamburg", "Florence", "Tallinn"]

# Required day contributions per city:
# Warsaw: 4, Venice: 3, Vilnius: 3, Salzburg: 4, Amsterdam: 2,
# Barcelona: 5, Paris: 2, Hamburg: 4, Florence: 5, Tallinn: 2.
req = [4, 3, 3, 4, 2, 5, 2, 4, 5, 2]

# Total required contributions = 4+3+3+4+2+5+2+4+5+2 = 34.
# We plan 25 base days. A flight day (when a flight is taken) counts for both
# the departure and arrival cities. Thus:
#   total_contrib = base_days + (#flights).
# Hence, we require (#flights) = 34 - 25 = 9.
# This partitions the itinerary into 10 segments (each segment is one visited city).

# Allowed direct flights (each tuple represents a direct flight from one city to another):
# 1. Paris and Venice
# 2. Barcelona and Amsterdam
# 3. Amsterdam and Warsaw
# 4. Amsterdam and Vilnius
# 5. Barcelona and Warsaw
# 6. Warsaw and Venice
# 7. Amsterdam and Hamburg
# 8. Barcelona and Hamburg
# 9. Barcelona and Florence
# 10. Barcelona and Venice
# 11. Paris and Hamburg
# 12. Paris and Vilnius
# 13. Paris and Amsterdam
# 14. Paris and Florence
# 15. Florence and Amsterdam
# 16. Vilnius and Warsaw
# 17. Barcelona and Tallinn
# 18. Paris and Warsaw
# 19. Tallinn and Warsaw
# 20. from Tallinn to Vilnius   (one-way: only Tallinn->Vilnius)
# 21. Amsterdam and Tallinn
# 22. Paris and Tallinn
# 23. Paris and Barcelona
# 24. Venice and Hamburg
# 25. Warsaw and Hamburg
# 26. Hamburg and Salzburg
# 27. Amsterdam and Venice
allowed_flights = [
    (6, 1), (1, 6),        # Paris <-> Venice
    (5, 4), (4, 5),        # Barcelona <-> Amsterdam
    (4, 0), (0, 4),        # Amsterdam <-> Warsaw
    (4, 2), (2, 4),        # Amsterdam <-> Vilnius
    (5, 0), (0, 5),        # Barcelona <-> Warsaw
    (0, 1), (1, 0),        # Warsaw <-> Venice
    (4, 7), (7, 4),        # Amsterdam <-> Hamburg
    (5, 7), (7, 5),        # Barcelona <-> Hamburg
    (5, 8), (8, 5),        # Barcelona <-> Florence
    (5, 1), (1, 5),        # Barcelona <-> Venice
    (6, 7), (7, 6),        # Paris <-> Hamburg
    (6, 2), (2, 6),        # Paris <-> Vilnius
    (6, 4), (4, 6),        # Paris <-> Amsterdam
    (6, 8), (8, 6),        # Paris <-> Florence
    (8, 4), (4, 8),        # Florence <-> Amsterdam
    (2, 0), (0, 2),        # Vilnius <-> Warsaw
    (5, 9), (9, 5),        # Barcelona <-> Tallinn
    (6, 0), (0, 6),        # Paris <-> Warsaw
    (9, 0), (0, 9),        # Tallinn <-> Warsaw
    (9, 2),               # from Tallinn to Vilnius (one-way)
    (4, 9), (9, 4),        # Amsterdam <-> Tallinn
    (6, 9), (9, 6),        # Paris <-> Tallinn
    (6, 5), (5, 6),        # Paris <-> Barcelona
    (1, 7), (7, 1),        # Venice <-> Hamburg
    (0, 7), (7, 0),        # Warsaw <-> Hamburg
    (7, 3), (3, 7),        # Hamburg <-> Salzburg
    (4, 1), (1, 4)         # Amsterdam <-> Venice
]

DAYS = 25  # number of base days (day indices 0..24)

# Create Z3 variables:
# c[d] is the base city on day d (0-indexed means day d corresponds to real Day d+1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is True if a flight occurs on day d (for d >= 1).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a new segment.
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Domain constraint: each day's base city is between 0 and 9.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < 10)

# Day 0 always starts a segment.
s.add(isSeg[0] == True)

# For days 1 to 24 define flights and segments.
for d in range(1, DAYS):
    # A flight occurs on day d if the city changes from day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs on day d, enforce that (c[d-1], c[d]) is an allowed flight.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Exactly 9 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 9)

# Ensure that the starting city of each segment is distinct (each visited city is unique).
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally, enforce that every city is visited at least once.
for city in range(10):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Compute day contributions for each city.
# Day 0 gives a contribution of 1 to c[0].
# For each day d (d>=1), if flight[d] then add 1 for departure (c[d-1]) and 1 for arrival (c[d]),
# otherwise add 1 for c[d] only.
counts = [Int(f"count_{city}") for city in range(10)]
for city in range(10):
    init = If(c[0] == city, 1, 0)
    daily = []
    for d in range(1, DAYS):
        daily.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == init + Sum(daily))
    s.add(counts[city] == req[city])

# Helper: inCityOnDay(d, target)
# This returns a condition ensuring that on day d, the itinerary "includes" the target city.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Event constraints:

# 1. Wedding in Salzburg (city 3) between day 22 and day 25.
#    Days 22 to 25 correspond to indices 21, 22, 23, 24.
wedding_salzburg = [inCityOnDay(d, 3) for d in [21, 22, 23, 24]]
s.add(Or(wedding_salzburg))

# 2. Meet friends at Barcelona (city 5) between day 2 and day 6.
#    These are days 2-6 -> indices 1, 2, 3, 4, 5.
friends_barcelona = [inCityOnDay(d, 5) for d in [1, 2, 3, 4, 5]]
s.add(Or(friends_barcelona))

# 3. Workshop in Paris (city 6) between day 1 and day 2.
#    Corresponding indices 0 and 1.
workshop_paris = [inCityOnDay(d, 6) for d in [0, 1]]
s.add(Or(workshop_paris))

# 4. Conference in Hamburg (city 7) "during day 19 and day 22".
#    Interpreting this as you must be in Hamburg on day 19 and day 22.
#    Day 19 -> index 18; day 22 -> index 21.
s.add(inCityOnDay(18, 7))
s.add(inCityOnDay(21, 7))

# 5. Meet a friend in Tallinn (city 9) between day 11 and day 12.
#    Days 11-12 -> indices 10 and 11.
meet_tallinn = [inCityOnDay(d, 9) for d in [10, 11]]
s.add(Or(meet_tallinn))

# Check the solution.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_index = m[c[d]].as_long()
        day_str = f"Day {d+1:2d}: {city_names[city_index]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[city_index]
            day_str += f" (Flight: {dep} -> {arr})"
        print(day_str)
    print("\nCity day contributions:")
    for i in range(10):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")