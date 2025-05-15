from z3 import *

# City indices:
# 0: London     – required 3 days.
# 1: Santorini  – required 6 days; with conference events on day 5 and day 10.
# 2: Istanbul   – required 3 days.
city_names = ["London", "Santorini", "Istanbul"]
required_credits = [3, 6, 3]
# Total required credits = 3 + 6 + 3 = 12

# Total itinerary days:
DAYS = 10
# Credit rules:
# Each non-flight day gives 1 credit to that day's city.
# A flight day (when a city change occurs) gives 1 credit for the departure and 1 for the arrival.
# Therefore, total credits = DAYS + (# flight-days).
# We need 12 credits, so number of flight-days must be 12 - 10 = 2.
REQUIRED_FLIGHTS = 2

# Allowed direct flights (bidirectional):
# Istanbul <-> London and London <-> Santorini.
allowed_flights = [
    (2, 0), (0, 2),  # Istanbul and London
    (0, 1), (1, 0)   # London and Santorini
]

s = Solver()

# Variables:
# c[d] : city at day d (0-indexed: d = 0,...,DAYS-1)
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] : Boolean variable indicating whether a flight (city change) occurs on day d.
# By convention, day 0 has no flight.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: each c[d] is one of {0, 1, 2}.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))
s.add(flight[0] == False)

# For days 1..DAYS-1, define flight indicator and enforce allowed transitions.
for d in range(1, DAYS):
    # A flight occurs on day d if the city on day d is different from that on day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    # When a flight happens on day d, ensure the flight (from c[d-1] to c[d]) is allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce that exactly REQUIRED_FLIGHTS flight-days occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function: returns an expression that is True if on day d the itinerary "includes" the target city.
# (On a flight day, both the departure and the arrival cities count.)
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits for each city.
# Day 0 gives 1 credit for city c[0].
# For each day d=1,...,DAYS-1:
#   - If no flight then that day adds 1 credit to c[d].
#   - If a flight occurs then add 1 credit to both the departure (c[d-1]) and arrival (c[d]).
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
    # Enforce required day credits.
    s.add(counts[city] == required_credits[city])
    # Ensure that each city is visited at least once somewhere in the itinerary.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event constraints:
# Conference in Santorini on day 5 and day 10.
# Here, we ensure that on day 5 (index 4) and day 10 (index 9) the itinerary includes Santorini (city 1).
s.add(inCityOnDay(4, 1))
s.add(inCityOnDay(9, 1))

# Solve the scheduling problem.
if s.check() == sat:
    model = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = model[c[d]].as_long()
        day_line = f"Day {d+1:02d}: {city_names[city_idx]}"
        if d >= 1 and model.evaluate(flight[d]):
            dep = model[c[d-1]].as_long()
            arr = model[c[d]].as_long()
            day_line += f" (Flight: {city_names[dep]} -> {city_names[arr]})"
        print(day_line)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]:11s}: {model.evaluate(counts[i])}")
else:
    print("No solution found.")