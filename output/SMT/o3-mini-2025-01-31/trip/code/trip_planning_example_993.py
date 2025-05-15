from z3 import *

# We have 7 European cities:
# 0: Riga       – 2 days
# 1: Frankfurt  – 3 days
# 2: Amsterdam  – 2 days, event: meet friend in Amsterdam between day 2 and day 3.
# 3: Vilnius    – 5 days, event: attend workshop in Vilnius between day 7 and day 11.
# 4: London     – 2 days
# 5: Stockholm  – 3 days, event: attend wedding in Stockholm between day 13 and day 15.
# 6: Bucharest  – 4 days
city_names = ["Riga", "Frankfurt", "Amsterdam", "Vilnius", "London", "Stockholm", "Bucharest"]
req = [2, 3, 2, 5, 2, 3, 4]  # required day contributions per city

# Total required contributions = 2+3+2+5+2+3+4 = 21.
# We have 15 base days. Since on a flight day both the departure and 
# arrival cities are counted, total contributions = 15 + (#flights).
# So we need #flights = 21 - 15 = 6.
# In other words, the 15 base days plus 6 extra flight contributions gives 21.
# This splits the trip into 7 segments, one per city.

DAYS = 15  # Base days (index 0 to 14 representing days 1 to 15)

# Allowed direct flights:
# "London and Amsterdam"         -> (London, Amsterdam) and (Amsterdam, London) : (4,2) and (2,4)
# "Vilnius and Frankfurt"         -> (Vilnius, Frankfurt) and (Frankfurt, Vilnius) : (3,1) and (1,3)
# "from Riga to Vilnius"          -> One-way: (Riga, Vilnius) : (0,3)
# "Riga and Stockholm"            -> Both ways: (Riga, Stockholm) and (Stockholm, Riga) : (0,5) and (5,0)
# "London and Bucharest"          -> (London, Bucharest) and (Bucharest, London) : (4,6) and (6,4)
# "Amsterdam and Stockholm"       -> (Amsterdam, Stockholm) and (Stockholm, Amsterdam) : (2,5) and (5,2)
# "Amsterdam and Frankfurt"       -> (Amsterdam, Frankfurt) and (Frankfurt, Amsterdam) : (2,1) and (1,2)
# "Frankfurt and Stockholm"       -> (Frankfurt, Stockholm) and (Stockholm, Frankfurt) : (1,5) and (5,1)
# "Bucharest and Riga"            -> (Bucharest, Riga) and (Riga, Bucharest) : (6,0) and (0,6)
# "Amsterdam and Riga"            -> (Amsterdam, Riga) and (Riga, Amsterdam) : (2,0) and (0,2)
# "Amsterdam and Bucharest"       -> (Amsterdam, Bucharest) and (Bucharest, Amsterdam) : (2,6) and (6,2)
# "Riga and Frankfurt"            -> (Riga, Frankfurt) and (Frankfurt, Riga) : (0,1) and (1,0)
# "Bucharest and Frankfurt"       -> (Bucharest, Frankfurt) and (Frankfurt, Bucharest) : (6,1) and (1,6)
# "London and Frankfurt"          -> (London, Frankfurt) and (Frankfurt, London) : (4,1) and (1,4)
# "London and Stockholm"          -> (London, Stockholm) and (Stockholm, London) : (4,5) and (5,4)
# "Amsterdam and Vilnius"         -> (Amsterdam, Vilnius) and (Vilnius, Amsterdam) : (2,3) and (3,2)
allowed_flights = [
    (4, 2), (2, 4),
    (3, 1), (1, 3),
    (0, 3),  # from Riga to Vilnius (one-way)
    (0, 5), (5, 0),
    (4, 6), (6, 4),
    (2, 5), (5, 2),
    (2, 1), (1, 2),
    (1, 5), (5, 1),
    (6, 0), (0, 6),
    (2, 0), (0, 2),
    (2, 6), (6, 2),
    (0, 1), (1, 0),
    (6, 1), (1, 6),
    (4, 1), (1, 4),
    (4, 5), (5, 4),
    (2, 3), (3, 2)
]

# Create Z3 variables:
# c[d] is the base city on day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean that indicates if a flight occurs on day d (for d>=1).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] indicates if day d is the start of a new segment (day 0 or a flight day).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain constraint: Each day, c[d] is one of 0 .. 6 (i.e. one of our 7 cities).
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < 7)

# 2. Day 0 starts a segment.
s.add(isSeg[0] == True)

# 3. For days 1 to 14, determine whether a flight occurs.
for d in range(1, DAYS):
    # A flight happens if the city changes from day d-1 to d.
    s.add(flight[d] == (c[d] != c[d-1]))
    # Day d is a segment start if a flight took place.
    s.add(isSeg[d] == flight[d])
    # If a flight occurs on day d, enforce that (c[d-1], c[d]) is an allowed connection.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly 6 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 6)

# 5. The starting city of each segment must be unique (ensuring one visit per city).
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally, enforce each city is visited at least once.
for city in range(7):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# 6. Compute day contributions for each city.
# Day 0: contribution 1 to c[0].
# For each day d>=1:
#   - If a flight occurs on day d, then add 1 to departure (c[d-1]) and 1 to arrival (c[d]).
#   - If no flight occurs, add 1 to the day's city c[d].
counts = [Int(f"count_{city}") for city in range(7)]
for city in range(7):
    init = If(c[0] == city, 1, 0)
    day_contrib = []
    for d in range(1, DAYS):
        day_contrib.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == init + Sum(day_contrib))
    s.add(counts[city] == req[city])

# Helper function: In a given day d, determine if the itinerary "includes" a target city.
# If day d is a flight day, then both departure and arrival are considered.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Event constraints:

# (a) Meet friend in Amsterdam (city 2) between day 2 and day 3.
# Day 2 and day 3 in the trip correspond to indices 1 and 2.
amsterdam_event = [inCityOnDay(d, 2) for d in [1, 2]]
s.add(Or(amsterdam_event))

# (b) Attend workshop in Vilnius (city 3) between day 7 and day 11.
# Days 7 to 11 correspond to indices 6, 7, 8, 9, 10.
vilnius_event = [inCityOnDay(d, 3) for d in range(6, 11)]
s.add(Or(vilnius_event))

# (c) Attend wedding in Stockholm (city 5) between day 13 and day 15.
# Days 13 to 15 correspond to indices 12, 13, and 14.
stockholm_event = [inCityOnDay(d, 5) for d in [12, 13, 14]]
s.add(Or(stockholm_event))

# Solve the model and print the itinerary.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_index = m[c[d]].as_long()
        day_str = f"Day {d+1:2d}: {city_names[city_index]}"
        # If a flight occurs on day d (d>=1), also print the flight details.
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[city_index]
            day_str += f" (Flight: {dep} -> {arr})"
        print(day_str)
    print("\nCity day contributions:")
    for i in range(7):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")