from z3 import *

# City indices and required credits:
# 0: Salzburg   – required 2 days.
# 1: Venice     – required 5 days.
# 2: Bucharest  – required 4 days.
# 3: Brussels   – required 2 days.
# 4: Hamburg    – required 4 days.
# 5: Copenhagen – required 4 days.
# 6: Nice       – required 3 days.
# 7: Zurich     – required 5 days.
# 8: Naples     – required 4 days.
city_names = ["Salzburg", "Venice", "Bucharest", "Brussels", "Hamburg", "Copenhagen", "Nice", "Zurich", "Naples"]
required_credits = [2, 5, 4, 2, 4, 4, 3, 5, 4]
# Total required credits = 2+5+4+2+4+4+3+5+4 = 33

# Total itinerary days:
DAYS = 25
# Credit rule:
# - On a day with no flight, you get 1 credit for the city of that day.
# - On a flight day (city change), you get 1 credit for the departure and 1 credit for the arrival.
# Thus total credits = DAYS + (# flight-days).
# To achieve 33 credits, we need (# flight-days) = 33 - 25 = 8.
REQUIRED_FLIGHTS = 8

# Allowed direct flights (bidirectional unless noted otherwise):
# "Zurich and Brussels"       : (7,3) and (3,7)
# "Bucharest and Copenhagen"   : (2,5) and (5,2)
# "Venice and Brussels"        : (1,3) and (3,1)
# "Nice and Zurich"            : (6,7) and (7,6)
# "Hamburg and Nice"           : (4,6) and (6,4)
# "Zurich and Naples"          : (7,8) and (8,7)
# "Hamburg and Bucharest"      : (4,2) and (2,4)
# "Zurich and Copenhagen"      : (7,5) and (5,7)
# "Bucharest and Brussels"     : (2,3) and (3,2)
# "Hamburg and Brussels"       : (4,3) and (3,4)
# "Venice and Naples"          : (1,8) and (8,1)
# "Venice and Copenhagen"      : (1,5) and (5,1)
# "Bucharest and Naples"       : (2,8) and (8,2)
# "Hamburg and Copenhagen"     : (4,5) and (5,4)
# "Venice and Zurich"          : (1,7) and (7,1)
# "Nice and Brussels"          : (6,3) and (3,6)
# "Hamburg and Venice"         : (4,1) and (1,4)
# "Copenhagen and Naples"      : (5,8) and (8,5)
# "Nice and Naples"            : (6,8) and (8,6)
# "Hamburg and Zurich"         : (4,7) and (7,4)
# "Salzburg and Hamburg"       : (0,4) and (4,0)
# "Zurich and Bucharest"       : (7,2) and (2,7)
# "Brussels and Naples"        : (3,8) and (8,3)
# "Copenhagen and Brussels"    : (5,3) and (3,5)
# "Venice and Nice"            : (1,6) and (6,1)
# "Nice and Copenhagen"        : (6,5) and (5,6)
allowed_flights = [
    (7,3), (3,7),
    (2,5), (5,2),
    (1,3), (3,1),
    (6,7), (7,6),
    (4,6), (6,4),
    (7,8), (8,7),
    (4,2), (2,4),
    (7,5), (5,7),
    (2,3), (3,2),
    (4,3), (3,4),
    (1,8), (8,1),
    (1,5), (5,1),
    (2,8), (8,2),
    (4,5), (5,4),
    (1,7), (7,1),
    (6,3), (3,6),
    (4,1), (1,4),
    (5,8), (8,5),
    (6,8), (8,6),
    (4,7), (7,4),
    (0,4), (4,0),
    (7,2), (2,7),
    (3,8), (8,3),
    (5,3), (3,5),
    (1,6), (6,1),
    (6,5), (5,6)
]

# Create the Z3 solver.
s = Solver()

# Variables:
# c[d]: city index on day d (0 <= d < DAYS)
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d]: Boolean indicating if a flight (change of city) occurs on day d.
# Convention: day 0 has no flight.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: each day's city is among 0..8.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))
s.add(flight[0] == False)

# For days 1 to DAYS-1, determine flight occurrence and allowed transitions.
for d in range(1, DAYS):
    # A flight occurs if today's city is different from yesterday's.
    s.add(flight[d] == (c[d] != c[d-1]))
    # If a flight occurs, then the transition (c[d-1] -> c[d]) must be an allowed flight.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly REQUIRED_FLIGHTS flight days.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Define helper: inCityOnDay(d, target)
# On a flight day, the day "covers" both the departure (previous day) and arrival (current day).
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits (contributions) for each city.
# Day 0 contributes 1 credit to city c[0].
# For each day d>=1:
#   - if no flight: add 1 credit for city c[d].
#   - if flight: add 1 credit for departure (c[d-1]) and 1 for arrival (c[d]).
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
    # Enforce the required day credits for each city.
    s.add(counts[city] == required_credits[city])
    # Ensure each city is visited at least once in the itinerary.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event constraints:

# 1. Meet friends in Brussels (city 3) between day 21 and day 22.
# Day numbers are 1-indexed, so day 21 and day 22 correspond to indices 20 and 21.
s.add(Or(inCityOnDay(20, 3), inCityOnDay(21, 3)))

# 2. Wedding in Copenhagen (city 5) between day 18 and day 21.
# That is days 18, 19, 20, 21 => zero-indexed 17,18,19,20.
s.add(Or([inCityOnDay(d, 5) for d in [17, 18, 19, 20]]))

# 3. Visit relatives in Nice (city 6) between day 9 and day 11.
# That is days 9, 10, 11 => zero-indexed 8,9,10.
s.add(Or([inCityOnDay(d, 6) for d in [8, 9, 10]]))

# 4. Workshop in Naples (city 8) between day 22 and day 25.
# That is days 22, 23, 24, 25 => zero-indexed 21,22,23,24.
s.add(Or([inCityOnDay(d, 8) for d in [21, 22, 23, 24]]))

# Solve the scheduling problem.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_str = f"Day {d+1:02d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = m[c[d-1]].as_long()
            arr = m[c[d]].as_long()
            day_str += f" (Flight: {city_names[dep]} -> {city_names[arr]})"
        print(day_str)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]:10s}: {m.evaluate(counts[i])}")
else:
    print("No solution found.")