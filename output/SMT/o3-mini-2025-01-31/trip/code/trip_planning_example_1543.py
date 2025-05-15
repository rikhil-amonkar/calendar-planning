from z3 import *

# City indices:
# 0: Prague      – required 3 days; event: attend a workshop in Prague between day 1 and day 3.
# 1: Warsaw      – required 4 days; event: meet friends in Warsaw between day 20 and day 23.
# 2: Dublin      – required 3 days
# 3: Athens      – required 3 days
# 4: Vilnius     – required 4 days
# 5: Porto       – required 5 days; event: attend a conference in Porto on day 16 and day 20.
# 6: London      – required 3 days; event: attend a wedding in London between day 3 and day 5.
# 7: Seville     – required 2 days
# 8: Lisbon      – required 5 days; event: visit relatives in Lisbon between day 5 and day 9.
# 9: Dubrovnik   – required 3 days
city_names = ["Prague", "Warsaw", "Dublin", "Athens", "Vilnius", 
              "Porto", "London", "Seville", "Lisbon", "Dubrovnik"]
required_credits = [3, 4, 3, 3, 4, 5, 3, 2, 5, 3]
# Total required credits = 3+4+3+3+4+5+3+2+5+3 = 35

# Total itinerary days:
DAYS = 26
# Credit accounting:
# - On a day with no flight, 1 credit is awarded for that day's city.
# - On a flight day (when the city changes) the day counts as 1 credit for the departure and 1 credit for the arrival.
# Therefore, total credits = DAYS + (# flight-days).
# We require 35 credits so (# flight-days) = 35 - 26 = 9.
REQUIRED_FLIGHTS = 9

# Allowed direct flights (bidirectional):
allowed_flights = [
    # Warsaw and Vilnius
    (1, 4), (4, 1),
    # Prague and Athens
    (0, 3), (3, 0),
    # London and Lisbon
    (6, 8), (8, 6),
    # Lisbon and Porto
    (8, 5), (5, 8),
    # Prague and Lisbon
    (0, 8), (8, 0),
    # London and Dublin
    (6, 2), (2, 6),
    # Athens and Vilnius
    (3, 4), (4, 3),
    # Athens and Dublin
    (3, 2), (2, 3),
    # Prague and London
    (0, 6), (6, 0),
    # London and Warsaw
    (6, 1), (1, 6),
    # Dublin and Seville
    (2, 7), (7, 2),
    # Seville and Porto
    (7, 5), (5, 7),
    # Lisbon and Athens
    (8, 3), (3, 8),
    # Dublin and Porto
    (2, 5), (5, 2),
    # Athens and Warsaw
    (3, 1), (1, 3),
    # Lisbon and Warsaw
    (8, 1), (1, 8),
    # Porto and Warsaw
    (5, 1), (1, 5),
    # Prague and Warsaw
    (0, 1), (1, 0),
    # Prague and Dublin
    (0, 2), (2, 0),
    # Athens and Dubrovnik
    (3, 9), (9, 3),
    # Lisbon and Dublin
    (8, 2), (2, 8),
    # Dubrovnik and Dublin
    (9, 2), (2, 9),
    # Lisbon and Seville
    (8, 7), (7, 8),
    # London and Athens
    (6, 3), (3, 6),
]

# Create Z3 solver instance.
s = Solver()

# Variables:
# c[d] represents the "base" city on day d (0-indexed, d = 0,1,...,DAYS-1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean variable indicating whether a flight occurs on day d.
# Convention: day 0 has no flight.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: each day's city is in {0, 1, ..., 9}.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# Day 0: no flight.
s.add(flight[0] == False)

# For days 1 to DAYS-1, define flight indicator and allowed flight transitions.
for d in range(1, DAYS):
    # A flight takes place on day d if the city differs from the previous day.
    s.add(flight[d] == (c[d] != c[d-1]))
    # If a flight occurs, then the flight from c[d-1] to c[d] must be in allowed_flights.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce that exactly REQUIRED_FLIGHTS flight-days occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function: inCityOnDay(d, target)
# This returns an expression that is true if on day d the itinerary "includes" the city 'target'.
# On a flight day, both the departure (day d-1) and the arrival (day d) are considered.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits for each city.
# Day 0 yields 1 credit for c[0]. For each subsequent day:
# - If there is no flight, add 1 credit to the day's city.
# - If there is a flight, add 1 credit to the departure (c[d-1]) and 1 credit to the arrival (c[d]).
counts = [Int(f"count_{i}") for i in range(len(city_names))]
for city in range(len(city_names)):
    base_credit = If(c[0] == city, 1, 0)
    daily = []
    for d in range(1, DAYS):
        daily.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == base_credit + Sum(daily))
    # Each city’s total credit must equal its required days.
    s.add(counts[city] == required_credits[city])
    # Ensure every city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event Constraints:

# 1. Workshop in Prague between day 1 and day 3.
# Days 1 to 3 correspond to indices 0, 1, and 2.
s.add(Or(inCityOnDay(0, 0), inCityOnDay(1, 0), inCityOnDay(2, 0)))

# 2. Meet friends in Warsaw between day 20 and day 23.
# Days 20 to 23 correspond to indices 19, 20, 21, and 22.
s.add(Or([inCityOnDay(d, 1) for d in range(19, 23)]))

# 3. Conference in Porto on day 16 and day 20.
# Day 16 -> index 15; day 20 -> index 19.
s.add(inCityOnDay(15, 5))
s.add(inCityOnDay(19, 5))

# 4. Wedding in London between day 3 and day 5.
# Days 3 to 5 correspond to indices 2, 3, and 4.
s.add(Or(inCityOnDay(2, 6), inCityOnDay(3, 6), inCityOnDay(4, 6)))

# 5. Visit relatives in Lisbon between day 5 and day 9.
# Days 5 to 9 correspond to indices 4, 5, 6, 7, and 8.
s.add(Or([inCityOnDay(d, 8) for d in range(4, 9)]))

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
        print(f"{city_names[i]:12s}: {m.evaluate(counts[i])}")
else:
    print("No solution found.")