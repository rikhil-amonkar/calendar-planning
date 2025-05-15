from z3 import *

# City indices:
# 0: Hamburg    – required 2 days
# 1: Zurich     – required 3 days; event: attend a wedding in Zurich between day 1 and day 3.
# 2: Helsinki   – required 2 days
# 3: Bucharest  – required 2 days
# 4: Split      – required 7 days; event: attend a conference in Split on day 4 and day 10.
city_names = ["Hamburg", "Zurich", "Helsinki", "Bucharest", "Split"]
req = [2, 3, 2, 2, 7]
# Total required day credits = 2+3+2+2+7 = 16

# Total itinerary days:
DAYS = 12
# Credit accounting:
#   - A day without a flight gives 1 credit (to the city for that day).
#   - A day with a flight (i.e., with a city change) gives 1 credit for the departure city and 1 for the arrival city.
# So total credits = DAYS + (# of flight-days).
# We need 16 credits, so if F is the number of flight-days: 12 + F = 16 → F = 4.
REQUIRED_FLIGHTS = 4

# Allowed direct flights (bidirectional):
# "Zurich and Helsinki"
# "Hamburg and Bucharest"
# "Helsinki and Hamburg"
# "Zurich and Hamburg"
# "Zurich and Bucharest"
# "Zurich and Split"
# "Helsinki and Split"
# "Split and Hamburg"
allowed_flights = [
    (1, 2), (2, 1),       # Zurich <-> Helsinki
    (0, 3), (3, 0),       # Hamburg <-> Bucharest
    (2, 0), (0, 2),       # Helsinki <-> Hamburg
    (1, 0), (0, 1),       # Zurich <-> Hamburg
    (1, 3), (3, 1),       # Zurich <-> Bucharest
    (1, 4), (4, 1),       # Zurich <-> Split
    (2, 4), (4, 2),       # Helsinki <-> Split
    (4, 0), (0, 4)        # Split <-> Hamburg
]

# Create a Z3 Solver instance.
s = Solver()

# Variables:
# c[d]: the “base” city on day d, for d = 0,1,...,DAYS-1.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d]: Boolean variable indicating whether a flight occurs on day d.
# By convention, we assume that day 0 has no flight.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: each day's city must be one of the 5 cities {0,...,4}.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# Day 0: no flight.
s.add(flight[0] == False)

# Define the flight relation for days 1..DAYS-1.
for d in range(1, DAYS):
    # A flight occurs on day d if the "base" city on day d differs from that on day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    # If a flight occurs on day d, enforce that the flight from c[d-1] to c[d] is allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly REQUIRED_FLIGHTS flight days.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function: inCityOnDay(d, target)
# Returns an expression that is true if on day d the itinerary "includes" the target city.
# Note: On a flight day, both the departure (c[d-1]) and the arrival (c[d]) are counted.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute the day-credits for each city based on the itinerary.
# Day 0 gives 1 credit for c[0].
# For each day d from 1 to DAYS-1:
#   - If no flight, day d gives 1 credit for city c[d].
#   - If a flight occurs, day d gives 1 credit for c[d-1] (departure) and 1 credit for c[d] (arrival).
counts = [Int(f"count_{i}") for i in range(len(city_names))]
for city in range(len(city_names)):
    base_credit = If(c[0] == city, 1, 0)
    daily_credits = []
    for d in range(1, DAYS):
        daily_credits.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == base_credit + Sum(daily_credits))
    # Enforce that each city's total credits equals the required number.
    s.add(counts[city] == req[city])
    # Also, ensure that each city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event Constraints:

# 1. Attend a wedding in Zurich between day 1 and day 3.
# That is, on at least one of day 1, day 2, or day 3 (indices 0,1,2), the itinerary must include Zurich (city 1).
s.add(Or(inCityOnDay(0, 1), inCityOnDay(1, 1), inCityOnDay(2, 1)))

# 2. Attend a conference in Split on day 4 and day 10.
# Day 4 corresponds to index 3 and day 10 corresponds to index 9.
s.add(inCityOnDay(3, 4))
s.add(inCityOnDay(9, 4))

# Solve the scheduling problem.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_str = f"Day {d+1:2d}: {city_names[city_idx]}"
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