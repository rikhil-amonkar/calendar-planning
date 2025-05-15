from z3 import *

# City indices:
# 0: Reykjavik  – desired 5 days.
# 1: Istanbul   – desired 4 days; event: meet friends in Istanbul between day 5 and day 8.
# 2: Edinburgh  – desired 5 days.
# 3: Oslo       – desired 2 days; event: visit relatives in Oslo between day 8 and day 9.
# 4: Stuttgart  – desired 3 days.
# 5: Bucharest  – desired 5 days.
city_names = ["Reykjavik", "Istanbul", "Edinburgh", "Oslo", "Stuttgart", "Bucharest"]
required_credits = [5, 4, 5, 2, 3, 5]
# Total required credits = 5 + 4 + 5 + 2 + 3 + 5 = 24

# Total itinerary days:
DAYS = 19
# Credit rule:
#   Each day without a flight gives 1 credit for that day's city.
#   On a flight day (city change) you get 1 credit for the departure and 1 for the arrival.
# So, total credits = DAYS + (# flight-days).
# We need: 19 + (# flights) = 24, hence #flight-days = 5.
REQUIRED_FLIGHTS = 5

# Allowed direct flights:
# Bucharest and Oslo: (5,3) and (3,5)
# Istanbul and Oslo: (1,3) and (3,1)
# from Reykjavik to Stuttgart: (0,4)   [unidirectional: only from Reykjavik to Stuttgart]
# Bucharest and Istanbul: (5,1) and (1,5)
# Stuttgart and Edinburgh: (4,2) and (2,4)
# Istanbul and Edinburgh: (1,2) and (2,1)
# Oslo and Reykjavik: (3,0) and (0,3)
# Istanbul and Stuttgart: (1,4) and (4,1)
# Oslo and Edinburgh: (3,2) and (2,3)
allowed_flights = [
    (5,3), (3,5),
    (1,3), (3,1),
    (0,4),  # unidirectional: from Reykjavik (0) to Stuttgart (4)
    (5,1), (1,5),
    (4,2), (2,4),
    (1,2), (2,1),
    (3,0), (0,3),
    (1,4), (4,1),
    (3,2), (2,3)
]

# Create the solver
s = Solver()

# Variables:
# c[d] is the city (an integer index) on day d (0-based index for days 0,...,DAYS-1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean indicating whether a flight occurs on day d.
# Convention: day 0 is not a flight day.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: each day's city must be one of the 6 cities.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))
s.add(flight[0] == False)

# For days 1 through DAYS-1, set flight indicator and enforce allowed transitions.
for d in range(1, DAYS):
    # Flight occurs if the city changes
    s.add(flight[d] == (c[d] != c[d-1]))
    # If a flight occurs, the transition must be one of the allowed flights.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly REQUIRED_FLIGHTS flight-days.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function: inCityOnDay
# Returns an expression that is True if day d "includes" the target city.
# For a flight day, both the departure (c[d-1]) and arrival (c[d]) count.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits for each city.
# Day 0 contributes 1 credit to the city c[0].
# For day d >= 1:
#   - If no flight: add 1 credit for c[d]
#   - If flight: add 1 credit for c[d-1] (departure) and 1 for c[d] (arrival)
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
    # Enforce the required credits for each city.
    s.add(counts[city] == required_credits[city])
    # Also ensure that every city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event Constraints:

# 1. Meet your friends at Istanbul (city index 1) between day 5 and day 8.
# That is, on at least one day among days 5,6,7,8 (indices 4,5,6,7).
s.add(Or([inCityOnDay(d, 1) for d in range(4, 8)]))

# 2. Visit relatives in Oslo (city index 3) between day 8 and day 9.
# That is, on at least one day among day 8 and day 9 (indices 7 and 8).
s.add(Or(inCityOnDay(7, 3), inCityOnDay(8, 3)))

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
        print(f"{city_names[i]:12s}: {m.evaluate(counts[i])}")
else:
    print("No solution found.")