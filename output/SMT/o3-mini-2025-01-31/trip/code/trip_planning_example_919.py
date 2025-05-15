from z3 import *

# City indices and required day credits:
# 0: Vienna   – required 4 days, and must be attended on day 1 and day 4 (i.e. indices 0 and 3) for the conference.
# 1: Milan    – required 2 days.
# 2: Rome     – required 3 days.
# 3: Riga     – required 2 days.
# 4: Lisbon   – required 3 days, with a relatives visit between day 11 and day 13 (indices 10,11,12).
# 5: Vilnius  – required 4 days.
# 6: Oslo     – required 3 days, with a friend meeting between day 13 and day 15 (indices 12,13,14).
city_names = ["Vienna", "Milan", "Rome", "Riga", "Lisbon", "Vilnius", "Oslo"]
required_credits = [4, 2, 3, 2, 3, 4, 3]
# Total required credits = 4+2+3+2+3+4+3 = 21

# Total itinerary days:
DAYS = 15
# Flight rule:
# - On a day without a flight, you get 1 credit for that day's city.
# - On a day with a flight (when you change cities) you get 1 credit for the departure and 1 for the arrival.
# So total credits = DAYS + (# flight-days)
# To get 21 credits, we require (# flight-days) = 21 - 15 = 6.
REQUIRED_FLIGHTS = 6

# Allowed direct flights (using city indices):
# Riga and Oslo                : (3,6) and (6,3)
# Rome and Oslo                : (2,6) and (6,2)
# Vienna and Milan             : (0,1) and (1,0)
# Vienna and Vilnius           : (0,5) and (5,0)
# Vienna and Lisbon            : (0,4) and (4,0)
# Riga and Milan               : (3,1) and (1,3)
# Lisbon and Oslo              : (4,6) and (6,4)
# from Rome to Riga (unidirectional): (2,3)
# Rome and Lisbon              : (2,4) and (4,2)
# Vienna and Riga              : (0,3) and (3,0)
# Vienna and Rome              : (0,2) and (2,0)
# Milan and Oslo               : (1,6) and (6,1)
# Vienna and Oslo              : (0,6) and (6,0)
# Vilnius and Oslo             : (5,6) and (6,5)
# from Riga to Vilnius (unidirectional): (3,5)
# Vilnius and Milan            : (5,1) and (1,5)
# Riga and Lisbon              : (3,4) and (4,3)
# Milan and Lisbon             : (1,4) and (4,1)
allowed_flights = [
    (3,6), (6,3),
    (2,6), (6,2),
    (0,1), (1,0),
    (0,5), (5,0),
    (0,4), (4,0),
    (3,1), (1,3),
    (4,6), (6,4),
    (2,3),            # unidirectional: Rome -> Riga
    (2,4), (4,2),
    (0,3), (3,0),
    (0,2), (2,0),
    (1,6), (6,1),
    (0,6), (6,0),
    (5,6), (6,5),
    (3,5),            # unidirectional: Riga -> Vilnius
    (5,1), (1,5),
    (3,4), (4,3),
    (1,4), (4,1)
]

s = Solver()

# Variables:
# c[d] represents the city index on day d (for d = 0,...,DAYS-1).
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Bool that indicates if a flight (city change) occurs on day d.
# By convention, day 0 has no flight.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints: each day d, c[d] is in range(0, len(city_names)).
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))
s.add(flight[0] == False)

# For days 1 to DAYS-1, enforce flight and allowed transition constraints.
for d in range(1, DAYS):
    # A flight occurs if the city on day d is different from day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    # If a flight occurs, then the transition (c[d-1] -> c[d]) must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly REQUIRED_FLIGHTS flight days.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function: inCityOnDay(d, target)
# On a flight day, a given day contributes to both departure (previous day) and arrival (current day)
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits for each city.
# Day 0 contributes 1 credit toward city c[0].
# For each day d >= 1:
#   - if no flight: add 1 credit for city c[d],
#   - if flight: add 1 credit for the departure (c[d-1]) and 1 for arrival (c[d]).
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
    # Each city must exactly meet the required day credits.
    s.add(counts[city] == required_credits[city])
    # And each city should be visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event constraints:

# 1. Conference in Vienna on day 1 and day 4.
#    Day 1 corresponds to index 0 and day 4 corresponds to index 3.
s.add(inCityOnDay(0, 0))  # Vienna on day 1.
s.add(inCityOnDay(3, 0))  # Vienna on day 4.

# 2. Relatives in Lisbon between day 11 and day 13.
#    That is for some day in {day 11, day 12, day 13} corresponding to indices 10, 11, 12.
s.add(Or(inCityOnDay(10, 4), inCityOnDay(11, 4), inCityOnDay(12, 4)))

# 3. Meeting a friend in Oslo between day 13 and day 15.
#    That is for some day in {day 13, day 14, day 15} corresponding to indices 12, 13, 14.
s.add(Or(inCityOnDay(12, 6), inCityOnDay(13, 6), inCityOnDay(14, 6)))

# Solve the scheduling problem.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        itinerary = f"Day {d+1:02d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = m[c[d-1]].as_long()
            arr = m[c[d]].as_long()
            itinerary += f" (Flight: {city_names[dep]} -> {city_names[arr]})"
        print(itinerary)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]:8s}: {m.evaluate(counts[i])}")
else:
    print("No solution found.")