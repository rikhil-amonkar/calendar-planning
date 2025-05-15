from z3 import *

# City indices and requirements:
# 0: Mykonos   – required 3 days.
# 1: Reykjavik – required 2 days; event: attend wedding in Reykjavik between day 9 and day 10.
# 2: Dublin    – required 5 days; event: attend annual show in Dublin from day 2 to day 6.
# 3: London    – required 5 days.
# 4: Helsinki  – required 4 days.
# 5: Hamburg   – required 2 days; event: meet friends in Hamburg between day 1 and day 2.
city_names = ["Mykonos", "Reykjavik", "Dublin", "London", "Helsinki", "Hamburg"]
required_credits = [3, 2, 5, 5, 4, 2]
# Total required credits = 3+2+5+5+4+2 = 21

# Total itinerary days:
DAYS = 16
# Flight rule:
#   On a day without a flight: 1 day credit for that city.
#   On a flight day (when you change cities) you get 1 credit for the departure and 1 for the arrival.
# So total credits = DAYS + (# flight-days)
# To meet 21 credits, we need (# flight-days) = 21 - 16 = 5.
REQUIRED_FLIGHTS = 5

# Allowed direct flights (bidirectional):
# "Dublin and London"       : (2,3) and (3,2)
# "Hamburg and Dublin"      : (5,2) and (2,5)
# "Helsinki and Reykjavik"  : (4,1) and (1,4)
# "Hamburg and London"      : (5,3) and (3,5)
# "Dublin and Helsinki"     : (2,4) and (4,2)
# "Reykjavik and London"    : (1,3) and (3,1)
# "London and Mykonos"      : (3,0) and (0,3)
# "Dublin and Reykjavik"    : (2,1) and (1,2)
# "Hamburg and Helsinki"    : (5,4) and (4,5)
# "Helsinki and London"     : (4,3) and (3,4)
allowed_flights = [
    (2,3), (3,2),
    (5,2), (2,5),
    (4,1), (1,4),
    (5,3), (3,5),
    (2,4), (4,2),
    (1,3), (3,1),
    (3,0), (0,3),
    (2,1), (1,2),
    (5,4), (4,5),
    (4,3), (3,4)
]

# Create the Z3 solver.
s = Solver()

# Variables:
# c[d] represents the city (by index) you are in on day d (d=0,...,DAYS-1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean indicating if a flight (city change) happens on day d.
# By convention, no flight happens on day 0.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: each day's city is one of the 6 cities.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))
s.add(flight[0] == False)

# For days 1 to DAYS-1, set flight indicator and enforce allowed transitions.
for d in range(1, DAYS):
    # A flight happens if today's city differs from yesterday's.
    s.add(flight[d] == (c[d] != c[d-1]))
    # If a flight occurs, the (previous city -> current city) transition must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly REQUIRED_FLIGHTS flight days.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function: inCityOnDay(d, target)
# On a flight day, the day "covers" both the departure and arrival cities.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits for each city:
# Day 0 gives 1 credit for the city c[0].
# For day d>=1:
#   - If there is no flight: add 1 credit for c[d].
#   - If there is a flight: add 1 credit for c[d-1] (departure) and 1 credit for c[d] (arrival).
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
    # Enforce required day credits.
    s.add(counts[city] == required_credits[city])
    # Also ensure each city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event constraints:

# 1. Wedding in Reykjavik (city index 1) between day 9 and day 10.
# Days 9 and 10 correspond to indices 8 and 9.
s.add(Or([inCityOnDay(d, 1) for d in range(8, 10)]))

# 2. Annual show in Dublin (city index 2) from day 2 to day 6.
# Corresponding to days 2 through 6 -> indices 1 to 5.
for d in range(1, 6):
    s.add(inCityOnDay(d, 2))

# 3. Meet friends in Hamburg (city index 5) between day 1 and day 2.
# These correspond to days 1 and 2 -> indices 0 and 1.
s.add(Or(inCityOnDay(0, 5), inCityOnDay(1, 5)))

# Solve the scheduling problem.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        info = f"Day {d+1:02d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = m[c[d-1]].as_long()
            arr = m[c[d]].as_long()
            info += f" (Flight: {city_names[dep]} -> {city_names[arr]})"
        print(info)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]:10s}: {m.evaluate(counts[i])}")
else:
    print("No solution found.")