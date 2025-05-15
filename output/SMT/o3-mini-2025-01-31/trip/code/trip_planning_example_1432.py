from z3 import *

# City indices:
# 0: Frankfurt   – required 4 days.
# 1: Salzburg    – required 5 days.
# 2: Athens      – required 5 days; event: attend a workshop in Athens between day 14 and day 18.
# 3: Reykjavik   – required 5 days.
# 4: Bucharest   – required 3 days.
# 5: Valencia    – required 2 days; event: annual show in Valencia from day 5 to day 6.
# 6: Vienna      – required 5 days; event: wedding in Vienna between day 6 and day 10.
# 7: Amsterdam   – required 3 days.
# 8: Stockholm   – required 3 days; event: meet a friend in Stockholm between day 1 and day 3.
# 9: Riga        – required 3 days; event: attend a conference in Riga on day 18 and day 20.
city_names = ["Frankfurt", "Salzburg", "Athens", "Reykjavik", "Bucharest", 
              "Valencia", "Vienna", "Amsterdam", "Stockholm", "Riga"]
required_credits = [4, 5, 5, 5, 3, 2, 5, 3, 3, 3]
# Total required credits = 4+5+5+5+3+2+5+3+3+3 = 38

# Total itinerary days:
DAYS = 29
# Credit rule:
# - A day with no flight contributes 1 credit for that day's city.
# - A day with a flight (city change) contributes 1 credit for the departure city and 1 for the arrival city.
# Hence, total credits = DAYS + (# flight-days).
# We require 38 credits, so the number of flight-days must equal 38 - 29 = 9.
REQUIRED_FLIGHTS = 9

# Allowed direct flights:
# "Valencia and Frankfurt"         : bidirectional (5,0) and (0,5)
# "Vienna and Bucharest"           : bidirectional (6,4) and (4,6)
# "from Valencia to Athens"        : unidirectional (5,2)
# "Athens and Bucharest"           : bidirectional (2,4) and (4,2)
# "Riga and Frankfurt"             : bidirectional (9,0) and (0,9)
# "Stockholm and Athens"           : bidirectional (8,2) and (2,8)
# "Amsterdam and Bucharest"        : bidirectional (7,4) and (4,7)
# "from Athens to Riga"            : unidirectional (2,9)
# "Amsterdam and Frankfurt"        : bidirectional (7,0) and (0,7)
# "Stockholm and Vienna"           : bidirectional (8,6) and (6,8)
# "Vienna and Riga"                : bidirectional (6,9) and (9,6)
# "Amsterdam and Reykjavik"        : bidirectional (7,3) and (3,7)
# "Reykjavik and Frankfurt"        : bidirectional (3,0) and (0,3)
# "Stockholm and Amsterdam"        : bidirectional (8,7) and (7,8)
# "Amsterdam and Valencia"         : bidirectional (7,5) and (5,7)
# "Vienna and Frankfurt"           : bidirectional (6,0) and (0,6)
# "Valencia and Bucharest"         : bidirectional (5,4) and (4,5)
# "Bucharest and Frankfurt"        : bidirectional (4,0) and (0,4)
# "Stockholm and Frankfurt"        : bidirectional (8,0) and (0,8)
# "Valencia and Vienna"            : bidirectional (5,6) and (6,5)
# "from Reykjavik to Athens"       : unidirectional (3,2)
# "Frankfurt and Salzburg"         : bidirectional (0,1) and (1,0)
# "Amsterdam and Vienna"           : bidirectional (7,6) and (6,7)
# "Stockholm and Reykjavik"        : bidirectional (8,3) and (3,8)
# "Amsterdam and Riga"             : bidirectional (7,9) and (9,7)
# "Stockholm and Riga"             : bidirectional (8,9) and (9,8)
# "Vienna and Reykjavik"           : bidirectional (6,3) and (3,6)
# "Amsterdam and Athens"           : bidirectional (7,2) and (2,7)
# "Athens and Frankfurt"           : bidirectional (2,0) and (0,2)
# "Vienna and Athens"              : bidirectional (6,2) and (2,6)
# "Riga and Bucharest"             : bidirectional (9,4) and (4,9)
allowed_flights = [
    (5,0), (0,5),
    (6,4), (4,6),
    (5,2),          # from Valencia to Athens
    (2,4), (4,2),
    (9,0), (0,9),
    (8,2), (2,8),
    (7,4), (4,7),
    (2,9),          # from Athens to Riga
    (7,0), (0,7),
    (8,6), (6,8),
    (6,9), (9,6),
    (7,3), (3,7),
    (3,0), (0,3),
    (8,7), (7,8),
    (7,5), (5,7),
    (6,0), (0,6),
    (5,4), (4,5),
    (4,0), (0,4),
    (8,0), (0,8),
    (5,6), (6,5),
    (3,2),          # from Reykjavik to Athens
    (0,1), (1,0),
    (7,6), (6,7),
    (8,3), (3,8),
    (7,9), (9,7),
    (8,9), (9,8),
    (6,3), (3,6),
    (7,2), (2,7),
    (2,0), (0,2),
    (6,2), (2,6),
    (9,4), (4,9)
]

# Create the solver
s = Solver()

# Variables:
# c[d] is the city at day d, for d=0,...,DAYS-1.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean indicating if a flight (city change) occurs on day d.
# By convention, day 0 has no flight.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]

# Domain constraints for cities.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))
s.add(flight[0] == False)

# For days 1..DAYS-1, define flight indicator and enforce allowed flight transitions.
for d in range(1, DAYS):
    # A flight happens on day d if the city changes
    s.add(flight[d] == (c[d] != c[d-1]))
    # If there's a flight, ensure the transition is allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Enforce exactly REQUIRED_FLIGHTS flight-days.
s.add(Sum([If(flight[d], 1, 0) for d in range(DAYS)]) == REQUIRED_FLIGHTS)

# Helper function: inCityOnDay(d, target)
# Returns an expression that is true if on day d the itinerary "includes" the target city.
# On a flight day, both the departure (c[d-1]) and arrival (c[d]) count.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Compute day credits for each city.
# Day 0 gives 1 credit for c[0]. For each subsequent day:
#  - If no flight on day d: add 1 credit for c[d].
#  - If flight on day d: add 1 for departure (c[d-1]) and 1 for arrival (c[d]).
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
    # Ensure every city is visited at least once.
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Event Constraints:

# 1. Workshop in Athens between day 14 and day 18.
# Days: 14,15,16,17,18 correspond to indices 13,14,15,16,17.
s.add(Or([inCityOnDay(d, 2) for d in range(13, 18)]))

# 2. Annual show in Valencia from day 5 to day 6.
# Days: 5 and 6 correspond to indices 4 and 5.
s.add(Or(inCityOnDay(4, 5), inCityOnDay(5, 5)))

# 3. Wedding in Vienna between day 6 and day 10.
# Days: 6,7,8,9,10 correspond to indices 5,6,7,8,9.
s.add(Or([inCityOnDay(d, 6) for d in range(5, 10)]))

# 4. Meet a friend in Stockholm between day 1 and day 3.
# Days: 1,2,3 correspond to indices 0,1,2.
s.add(Or([inCityOnDay(d, 8) for d in range(0, 3)]))

# 5. Conference in Riga on day 18 and day 20.
# Day 18 -> index 17, Day 20 -> index 19.
s.add(inCityOnDay(17, 9))
s.add(inCityOnDay(19, 9))

# Solve the scheduling problem.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_line = f"Day {d+1:02d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = m[c[d-1]].as_long()
            arr = m[c[d]].as_long()
            day_line += f" (Flight: {city_names[dep]} -> {city_names[arr]})"
        print(day_line)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]:11s}: {m.evaluate(counts[i])}")
else:
    print("No solution found.")