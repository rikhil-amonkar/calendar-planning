from z3 import *

# City indices and required day credits:
# 0: Madrid  - required 4 days.
# 1: Dublin  - required 3 days.
# 2: Tallinn - required 2 days; workshop between day 6 and day 7.
city_names = ["Madrid", "Dublin", "Tallinn"]
required_credits = [4, 3, 2]
# Total required credits = 4 + 3 + 2 = 9

# Total itinerary days:
DAYS = 7
# Flight day rule:
#  - On a day without flight: 1 credit for that day's city.
#  - On a flight day (city change) you get 1 credit for departure and 1 credit for arrival.
# Therefore, total credits = DAYS + (# flight days). To equal 9, we need (# flight days)=9-7=2.
REQUIRED_FLIGHTS = 2

# Allowed direct flights (bidirectional):
# Madrid <--> Dublin: (0,1) and (1,0)
# Dublin <--> Tallinn: (1,2) and (2,1)
allowed_flights = [
    (0, 1), (1, 0),
    (1, 2), (2, 1)
]

# Create Z3 solver.
s = Solver()

# Variables:
# c[d]: the city you are in on day d (for d = 0 ... DAYS-1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d]: Boolean indicating if a flight occurs on day d.
# By convention day 0 no flight.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: each day's city index is in {0, 1, 2}.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))
s.add(flight[0] == False)

# Define flight occurrence and enforce allowed transitions.
for d in range(1, DAYS):
    # A flight occurs if today's city differs from yesterday's.
    s.add(flight[d] == (c[d] != c[d-1]))
    # If a flight occurs then the transition (c[d-1] -> c[d]) must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Exactly REQUIRED_FLIGHTS flight days.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function: inCityOnDay(d, target)
# On a flight day, the day counts for both the departure and arrival.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits (contributions) for each city.
# Day 0 gives 1 credit for city c[0].
# For day d >= 1:
#    - if no flight: add 1 credit for city c[d]
#    - if flight: add 1 credit for departure (c[d-1]) and 1 credit for arrival (c[d])
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
    # Enforce required credit for each city.
    s.add(counts[city] == required_credits[city])
    # Ensure each city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event constraint:
# Workshop in Tallinn between day 6 and day 7 (days are 1-indexed); i.e., day6 or day7 => indices 5 or 6.
s.add(Or(inCityOnDay(5, 2), inCityOnDay(6, 2)))  # 2 is Tallinn

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
        print(f"{city_names[i]:8s}: {m.evaluate(counts[i])}")
else:
    print("No solution found.")