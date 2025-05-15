from z3 import *

# City indices and requirements:
# 0: Split  – 5 days; event: annual show in Split between day 7 and day 11.
# 1: Oslo   – 2 days.
# 2: London – 7 days; event: visit relatives in London between day 1 and day 7.
# 3: Porto  – 5 days.
city_names = ["Split", "Oslo", "London", "Porto"]
req = [5, 2, 7, 5]  # Total required day contributions = 5 + 2 + 7 + 5 = 19

# Total base days = 16.
# On a non-flight day, the itinerary gets 1 day credit.
# On a flight day, both the departure and arrival cities get a credit.
# Therefore, total credits = base_days + (# flights) = 16 + (# flights).
# To meet 19 credits, we need exactly 3 flights.
# With 3 flights, the itinerary is partitioned into 4 segments (one for each city).
DAYS = 16

# Allowed direct flights between cities (bidirectional unless specified otherwise):
# "London and Oslo": (London, Oslo) and (Oslo, London) => (2,1) and (1,2)
# "Split and Oslo":   (Split, Oslo) and (Oslo, Split)   => (0,1) and (1,0)
# "Oslo and Porto":   (Oslo, Porto) and (Porto, Oslo)   => (1,3) and (3,1)
# "London and Split": (London, Split) and (Split, London) => (2,0) and (0,2)
allowed_flights = [
    (2, 1), (1, 2),
    (0, 1), (1, 0),
    (1, 3), (3, 1),
    (2, 0), (0, 2)
]

# Create Z3 variables:
# c[d]: base city on day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d]: True if there is a flight on day d (for d>=1; day 0 is the starting city so no flight)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d]: True if day d is the start of a new city segment (either day 0 or when a flight occurs)
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain: each c[d] must be in {0, 1, 2, 3}.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 is the start of a segment.
s.add(isSeg[0] == True)

# 3. For each day d>=1, determine if a flight occurs and enforce allowed flight transitions.
for d in range(1, DAYS):
    # Flight occurs when the base city changes from day d-1.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If flight occurs, ensure (c[d-1], c[d]) is in allowed_flights.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. There must be exactly 3 flights.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 3)

# 5. The starting base city of each segment (day 0 and days with a flight) must be distinct.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally, enforce that every city is visited.
for city in range(len(city_names)):
    s.add(Or([And(isSeg[d], c[d] == city) for d in range(DAYS)]))

# 6. Compute the day contributions for each city.
# Day 0 gives a credit for the city c[0].
# For day d >= 1:
#   - If flight occurs, both the departure (c[d-1]) and arrival (c[d]) get a credit.
#   - If no flight occurs, then only the current day's city (c[d]) gets a credit.
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
    s.add(counts[city] == req[city])

# Helper: on day d, the itinerary "includes" a target city.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Event constraints:
# (a) Annual show in Split (city 0) between day 7 and day 11.
# That is, for some day d in indices 6 to 10, the itinerary must include Split.
annual_show = [inCityOnDay(d, 0) for d in range(6, 11)]
s.add(Or(annual_show))

# (b) Relatives in London (city 2) between day 1 and day 7.
# That is, for some day d in indices 0 to 6, the itinerary must include London.
visit_relatives = [inCityOnDay(d, 2) for d in range(0, 7)]
s.add(Or(visit_relatives))

# Solve the model and output the itinerary.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_idx = m[c[d]].as_long()
        day_str = f"Day {d+1:2d}: {city_names[city_idx]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[city_idx]
            day_str += f" (Flight: {dep} -> {arr})"
        print(day_str)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")