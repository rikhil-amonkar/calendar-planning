from z3 import *

# City indices and names:
# 0: Prague         (5 days; event: annual show in Prague from day 5 to day 9)
# 1: Brussels       (2 days)
# 2: Riga           (2 days; event: meet friends in Riga between day 15 and day 16)
# 3: Munich         (2 days)
# 4: Seville        (3 days)
# 5: Stockholm      (2 days; event: attend conference in Stockholm during day 16 and day 17)
# 6: Istanbul       (2 days)
# 7: Amsterdam      (3 days)
# 8: Vienna         (5 days; event: meet a friend in Vienna between day 1 and day 5)
# 9: Split          (3 days; event: visit relatives in Split between day 11 and day 13)
city_names = ["Prague", "Brussels", "Riga", "Munich", "Seville", "Stockholm",
              "Istanbul", "Amsterdam", "Vienna", "Split"]

# Required day counts per city.
req = [5, 2, 2, 2, 3, 2, 2, 3, 5, 3]
# Total required contributions = sum(req) = 5+2+2+2+3+2+2+3+5+3 = 29.
# We have 20 base days. Since a flight day (i.e. a day on which a flight happens) counts for both the departure and arrival,
# the total contributions = 20 + (# flights). To achieve 29 we need 20 + f = 29, i.e. f = 9 flights.
# That implies that the itinerary is segmented into 10 segments – each segment corresponding to a unique city.

# Allowed direct flights (bidirectional unless noted otherwise)
# Note: In the provided list, one flight is given as "from Riga to Munich". We treat that as a one-way allowed flight.
allowed_flights = [
    # Riga and Stockholm
    (2, 5), (5, 2),
    # Stockholm and Brussels
    (5, 1), (1, 5),
    # Istanbul and Munich
    (6, 3), (3, 6),
    # Istanbul and Riga
    (6, 2), (2, 6),
    # Prague and Split
    (0, 9), (9, 0),
    # Vienna and Brussels
    (8, 1), (1, 8),
    # Vienna and Riga
    (8, 2), (2, 8),
    # Split and Stockholm
    (9, 5), (5, 9),
    # Munich and Amsterdam
    (3, 7), (7, 3),
    # Split and Amsterdam
    (9, 7), (7, 9),
    # Amsterdam and Stockholm
    (7, 5), (5, 7),
    # Amsterdam and Riga
    (7, 2), (2, 7),
    # Vienna and Stockholm
    (8, 5), (5, 8),
    # Vienna and Istanbul
    (8, 6), (6, 8),
    # Vienna and Seville
    (8, 4), (4, 8),
    # Istanbul and Amsterdam
    (6, 7), (7, 6),
    # Munich and Brussels
    (3, 1), (1, 3),
    # Prague and Munich
    (0, 3), (3, 0),
    # from Riga to Munich (one-way ONLY)
    (2, 3),
    # Prague and Amsterdam
    (0, 7), (7, 0),
    # Prague and Brussels
    (0, 1), (1, 0),
    # Prague and Istanbul
    (0, 6), (6, 0),
    # Istanbul and Stockholm
    (6, 5), (5, 6),
    # Vienna and Prague
    (8, 0), (0, 8),
    # Munich and Split
    (3, 9), (9, 3),
    # Vienna and Amsterdam
    (8, 7), (7, 8),
    # Prague and Stockholm
    (0, 5), (5, 0),
    # Brussels and Seville
    (1, 4), (4, 1),
    # Munich and Stockholm
    (3, 5), (5, 3),
    # Istanbul and Brussels
    (6, 1), (1, 6),
    # Amsterdam and Seville
    (7, 4), (4, 7),
    # Vienna and Split
    (8, 9), (9, 8),
    # Munich and Seville
    (3, 4), (4, 3),
    # Riga and Brussels
    (2, 1), (1, 2),
    # Prague and Riga
    (0, 2), (2, 0),
    # Vienna and Munich
    (8, 3), (3, 8)
]

# Total itinerary base days
DAYS = 20

# Create Z3 variables.
# c[d]: integer variable for the base city on day d (0-indexed representing day d+1)
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d]: Boolean variable indicating if a flight occurs on day d (for d>=1)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d]: Boolean variable indicating that day d is the start of a new segment (always True for day 0 and when a flight occurs)
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Constrain each base city to be one of the 10 cities.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < 10)

# Day 0 is always the start of a segment.
s.add(isSeg[0] == True)

# For days 1..(DAYS-1), define flight indicator and segment flag.
for d in range(1, DAYS):
    # A flight occurs on day d if the base city changes from day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs on day d, then (c[d-1], c[d]) must be an allowed flight.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# Exactly 9 flights occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 9)

# The starting city of each segment (day 0 and any day with a flight) must be distinct.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally ensure that every city appears at least once.
for city in range(10):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Calculate day contributions for each city.
# On day 0, contribute 1 to the city c[0].
# For each day d from 1 to DAYS-1:
#   if a flight occurs, then add 1 for the previous base city and 1 for the current base city;
#   otherwise add 1 for the current base city.
counts = [Int(f"count_{i}") for i in range(10)]
for i in range(10):
    initial = If(c[0] == i, 1, 0)
    daily = []
    for d in range(1, DAYS):
        daily.append(
            If(flight[d],
               (If(c[d-1] == i, 1, 0) + If(c[d] == i, 1, 0)),
               If(c[d] == i, 1, 0)
            )
        )
    s.add(counts[i] == initial + Sum(daily))
    s.add(counts[i] == req[i])

# Helper function: inCityOnDay(d, target) returns a constraint that day d "includes" the target city.
# If a flight occurs on day d, then the day is counted for both the departure and arrival cities.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Event constraints:
# 1. Attend the annual show in Prague (city 0) from day 5 to day 9 (indices 4 to 8):
prague_show = [inCityOnDay(d, 0) for d in range(4, 9)]
s.add(Or(prague_show))

# 2. Meet friends in Riga (city 2) between day 15 and day 16 (indices 14 and 15):
riga_friends = [inCityOnDay(d, 2) for d in [14, 15]]
s.add(Or(riga_friends))

# 3. Attend the conference in Stockholm (city 5) during day 16 and day 17 (indices 15 and 16):
stockholm_conf = [inCityOnDay(d, 5) for d in [15, 16]]
s.add(Or(stockholm_conf))

# 4. Meet a friend in Vienna (city 8) between day 1 and day 5 (indices 0 to 4):
vienna_friend = [inCityOnDay(d, 8) for d in range(0, 5)]
s.add(Or(vienna_friend))

# 5. Visit relatives in Split (city 9) between day 11 and day 13 (indices 10 to 12):
split_relatives = [inCityOnDay(d, 9) for d in range(10, 13)]
s.add(Or(split_relatives))

# Check for a solution.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        base_city = m[c[d]].as_long()
        day_str = f"Day {d+1:2d}: In {city_names[base_city]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[base_city]
            day_str += f" (Flight: {dep} -> {arr})"
        print(day_str)
    print("\nCity day counts:")
    for i in range(10):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")