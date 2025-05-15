from z3 import *

# City indices and requirements:
# 0: Mykonos  – required 3 days; event: attend wedding in Mykonos between day 4 and day 6.
# 1: Riga     – required 3 days.
# 2: Munich   – required 4 days.
# 3: Bucharest– required 4 days.
# 4: Rome     – required 4 days; event: attend conference in Rome on day 1 and day 4.
# 5: Nice     – required 3 days.
# 6: Krakow   – required 2 days; event: attend annual show in Krakow between day 16 and day 17.
city_names = ["Mykonos", "Riga", "Munich", "Bucharest", "Rome", "Nice", "Krakow"]
required_credits = [3, 3, 4, 4, 4, 3, 2]
# Total required credits = 3 + 3 + 4 + 4 + 4 + 3 + 2 = 23

# Total itinerary days:
DAYS = 17
# Credit rule:
# - On a day with no flight, you get 1 credit for the city.
# - On a flight day (when you change cities), you get 1 credit for the departure and 1 for the arrival city.
# Hence, total credits = DAYS + (# flight-days).
# We need: 17 + (# flights) = 23 -> # flights = 6.
REQUIRED_FLIGHTS = 6

# Allowed direct flights:
# "Nice and Riga"            : (5,1) and (1,5)
# "Bucharest and Munich"      : (3,2) and (2,3)
# "Mykonos and Munich"        : (0,2) and (2,0)
# "Riga and Bucharest"        : (1,3) and (3,1)
# "Rome and Nice"             : (4,5) and (5,4)
# "Rome and Munich"           : (4,2) and (2,4)
# "Mykonos and Nice"          : (0,5) and (5,0)
# "Rome and Mykonos"          : (4,0) and (0,4)
# "Munich and Krakow"         : (2,6) and (6,2)
# "Rome and Bucharest"        : (4,3) and (3,4)
# "Nice and Munich"           : (5,2) and (2,5)
# "from Riga to Munich"       : unidirectional, (1,2)
# "from Rome to Riga"         : unidirectional, (4,1)
allowed_flights = [
    (5, 1), (1, 5),
    (3, 2), (2, 3),
    (0, 2), (2, 0),
    (1, 3), (3, 1),
    (4, 5), (5, 4),
    (4, 2), (2, 4),
    (0, 5), (5, 0),
    (4, 0), (0, 4),
    (2, 6), (6, 2),
    (4, 3), (3, 4),
    (5, 2), (2, 5),
    (1, 2),  # from Riga to Munich (unidirectional)
    (4, 1)   # from Rome to Riga (unidirectional)
]

# Create the solver.
s = Solver()

# Variables:
# c[d] denotes the city (by its index) on day d (for d = 0, 1, ..., DAYS-1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is Boolean indicating if a flight (i.e. a city change) occurs on day d.
# By convention, day 0 is not a flight day.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: each day's city is between 0 and len(city_names)-1.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))
s.add(flight[0] == False)

# For days 1...DAYS-1, set the flight indicator and enforce allowed transitions.
for d in range(1, DAYS):
    # A flight occurs on day d if the city changes from the previous day.
    s.add(flight[d] == (c[d] != c[d-1]))
    # If a flight occurs, then the transition from c[d-1] to c[d] must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Ensure exactly REQUIRED_FLIGHTS days have a flight.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function: inCityOnDay(d, target)
# Returns a Z3 Boolean expression that is True if day d "includes" the target city.
# On a flight day, both the departure (c[d-1]) and arrival (c[d]) cities are considered.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Calculate day credits for each city.
# Day 0 contributes 1 credit for the city c[0].
# For each subsequent day d (d>=1):
#   - If no flight on day d, add 1 credit for c[d].
#   - If a flight occurs, add 1 credit for c[d-1] and 1 for c[d].
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
    # Enforce the exact required day credits for each city.
    s.add(counts[city] == required_credits[city])
    # Also ensure that every city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event constraints:

# 1. Wedding in Mykonos (city 0) between day 4 and day 6.
# Days 4, 5, 6 correspond to indices 3,4,5.
s.add(Or([inCityOnDay(d, 0) for d in range(3, 6)]))

# 2. Conference in Rome (city 4) on day 1 and day 4.
# Day 1 -> index 0; Day 4 -> index 3.
s.add(inCityOnDay(0, 4))
s.add(inCityOnDay(3, 4))

# 3. Annual show in Krakow (city 6) from day 16 to day 17.
# Days 16 and 17 correspond to indices 15 and 16.
s.add(Or(inCityOnDay(15, 6), inCityOnDay(16, 6)))

# Solve the scheduling problem.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_info = f"Day {d+1:02d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = m[c[d-1]].as_long()
            arr = m[c[d]].as_long()
            day_info += f" (Flight: {city_names[dep]} -> {city_names[arr]})"
        print(day_info)
    
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]:10s}: {m.evaluate(counts[i])}")
else:
    print("No solution found.")