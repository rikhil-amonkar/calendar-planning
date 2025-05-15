from z3 import *

# City indices and names:
# 0: Tallinn    (2 days)
# 1: Bucharest  (4 days; event: visit relatives in Bucharest between day 1 and day 4)
# 2: Seville    (5 days; event: meet friends in Seville between day 8 and day 12)
# 3: Stockholm  (5 days)
# 4: Munich     (5 days; event: wedding in Munich between day 4 and day 8)
# 5: Milan      (2 days)
city_names = ["Tallinn", "Bucharest", "Seville", "Stockholm", "Munich", "Milan"]
req = [2, 4, 5, 5, 5, 2]  # required day contributions per city

# Total required contributions = 2+4+5+5+5+2 = 23.
# We have 18 base days. If a flight is taken, the day counts for both departure and arrival.
# Total contribution = base days + (#flights).
# Thus, #flights = 23 - 18 = 5.
# This implies 6 segments (each city appears exactly once).

# Allowed direct flights (bidirectional):
# Milan and Stockholm: (5,3) and (3,5)
# Munich and Stockholm: (4,3) and (3,4)
# Bucharest and Munich: (1,4) and (4,1)
# Munich and Seville: (4,2) and (2,4)
# Stockholm and Tallinn: (3,0) and (0,3)
# Munich and Milan: (4,5) and (5,4)
# Munich and Tallinn: (4,0) and (0,4)
# Seville and Milan: (2,5) and (5,2)
allowed_flights = [
    (5, 3), (3, 5),
    (4, 3), (3, 4),
    (1, 4), (4, 1),
    (4, 2), (2, 4),
    (3, 0), (0, 3),
    (4, 5), (5, 4),
    (4, 0), (0, 4),
    (2, 5), (5, 2)
]

DAYS = 18  # Base days: indices 0 .. 17

# Create Z3 variables.
# c[d] represents the base city on day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is True if a flight is taken on day d (for d>=1).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] indicates if day d is the start of a segment (day 0 and any day when a flight occurs).
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Each day d, the city must be between 0 and 5.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < 6)

# Day 0 is always a segment start.
s.add(isSeg[0] == True)

# For days 1 to DAYS-1, define flight and segment relations.
for d in range(1, DAYS):
    # A flight occurs on day d if the city changes from the previous day.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs on day d, then the flight route must be allowed.
    s.add(Implies(flight[d], 
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Exactly 5 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 5)

# Enforce that each segment's starting city is distinct (so each city is used exactly once).
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally enforce that every city is visited at least once.
for city in range(6):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Compute day contributions for each city.
# Day 0 contributes 1 to c[0].
# For day d>=1:
# - if flight[d] is True, then it contributes 1 day to both c[d-1] and c[d].
# - if no flight, then only c[d] gets 1 day.
counts = [Int(f"count_{city}") for city in range(6)]
for city in range(6):
    init = If(c[0] == city, 1, 0)
    daily = []
    for d in range(1, DAYS):
        daily.append(
            If(flight[d],
                (If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0)),
                If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == init + Sum(daily))
    s.add(counts[city] == req[city])

# Helper function: inCityOnDay(d, target)
# This returns a condition that on day d the itinerary "includes" the target city.
# If a flight is taken on day d, then both the departure (c[d-1]) and arrival (c[d]) are considered.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Event constraints:

# 1. Visit relatives in Bucharest (city 1) between day 1 and day 4.
#    Days 1 to 4 -> indices 0, 1, 2, 3.
booking_bucharest = [inCityOnDay(d, 1) for d in range(0, 4)]
s.add(Or(booking_bucharest))

# 2. Meet friends at Seville (city 2) between day 8 and day 12.
#    Days 8 to 12 -> indices 7, 8, 9, 10, 11.
friends_seville = [inCityOnDay(d, 2) for d in range(7, 12)]
s.add(Or(friends_seville))

# 3. Attend a wedding in Munich (city 4) between day 4 and day 8.
#    Days 4 to 8 -> indices 3, 4, 5, 6, 7.
wedding_munich = [inCityOnDay(d, 4) for d in range(3, 8)]
s.add(Or(wedding_munich))

# Check for a solution.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_index = m[c[d]].as_long()
        day_info = f"Day {d+1:2d}: {city_names[city_index]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep_city = city_names[m[c[d-1]].as_long()]
            arr_city = city_names[city_index]
            day_info += f" (Flight: {dep_city} -> {arr_city})"
        print(day_info)
    print("\nCity day contributions:")
    for i in range(6):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")