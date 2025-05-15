from z3 import *

# City indices and requirements:
# 0: Helsinki   – 2 days; event: attend a workshop in Helsinki between day 1 and day 2.
# 1: Warsaw     – 3 days; event: visit relatives in Warsaw between day 9 and day 11.
# 2: Madrid     – 4 days.
# 3: Split      – 4 days.
# 4: Reykjavik  – 2 days; event: meet a friend in Reykjavik between day 8 and day 9.
# 5: Budapest   – 4 days.
city_names = ["Helsinki", "Warsaw", "Madrid", "Split", "Reykjavik", "Budapest"]
req = [2, 3, 4, 4, 2, 4]  # Total required day credits = 2+3+4+4+2+4 = 19

# Total base days = 14.
# On a day with no flight, you get 1 credit.
# On a flight day (where you fly from A to B on that day) both A and B receive 1 credit.
# Hence, total credits = 14 + (# flights) = 19 => We need exactly 5 flights.
# That partitions the trip into 6 segments (one for each city visited).
DAYS = 14
REQUIRED_FLIGHTS = 5

# Allowed direct flights.
# Provided flights (using our city indices):
# Helsinki and Reykjavik:           (0,4) and (4,0)
# Budapest and Warsaw:              (5,1) and (1,5)
# Madrid and Split:                 (2,3) and (3,2)
# Helsinki and Split:               (0,3) and (3,0)
# Helsinki and Madrid:              (0,2) and (2,0)
# Helsinki and Budapest:            (0,5) and (5,0)
# Reykjavik and Warsaw:             (4,1) and (1,4)
# Helsinki and Warsaw:              (0,1) and (1,0)
# Madrid and Budapest:              (2,5) and (5,2)
# Budapest and Reykjavik:           (5,4) and (4,5)
# Madrid and Warsaw:                (2,1) and (1,2)
# Warsaw and Split:                 (1,3) and (3,1)
# from Reykjavik to Madrid (unidirectional): (4,2)
allowed_flights = [
    (0,4), (4,0),
    (5,1), (1,5),
    (2,3), (3,2),
    (0,3), (3,0),
    (0,2), (2,0),
    (0,5), (5,0),
    (4,1), (1,4),
    (0,1), (1,0),
    (2,5), (5,2),
    (5,4), (4,5),
    (2,1), (1,2),
    (1,3), (3,1),
    (4,2)
]

# Create Z3 variables:
# c[d]: the base city on day d (0 <= d < DAYS)
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d]: True if a flight occurs on day d (for d>=1; day 0 is start so no flight)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d]: True if day d is the start of a segment (i.e. day 0 or a day on which a flight occurs)
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain constraints: each day's base city must be one of the 6 cities.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day 0 is always a segment start.
s.add(isSeg[0] == True)

# 3. For each day d >= 1, determine if a flight occurs and enforce allowed transitions.
for d in range(1, DAYS):
    # A flight occurs if today's city is different from yesterday's.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs, then the transition (c[d-1] -> c[d]) must be an allowed direct flight.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly REQUIRED_FLIGHTS flights must occur (among days 1..DAYS-1).
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == REQUIRED_FLIGHTS)

# 5. Distinct Segment Constraint:
# The starting city of each segment (day 0 and any day with a flight) must be distinct,
# ensuring that each of the 6 cities is visited exactly once.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))
# Ensure every city is visited as a segment start.
for city in range(len(city_names)):
    s.add(Or([And(isSeg[d], c[d] == city) for d in range(DAYS)]))

# 6. Compute day contributions for each city.
# Day 0: contributes 1 to city c[0].
# For each day d>=1:
#   If flight occurs on day d, then add 1 credit to the city on day d-1 and 1 credit to the city on day d.
#   Otherwise, add 1 credit to the city on day d.
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

# Helper: returns an expression that checks if on day d, the itinerary "includes" city 'target'
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Event Constraints:
# (a) Helsinki workshop (city 0) between day 1 and day 2 (i.e. indices 0 and 1)
helsinki_workshop = [inCityOnDay(d, 0) for d in [0, 1]]
s.add(Or(helsinki_workshop))

# (b) Relatives in Warsaw (city 1) between day 9 and day 11 (i.e. indices 8, 9, and 10)
warsaw_relatives = [inCityOnDay(d, 1) for d in [8, 9, 10]]
s.add(Or(warsaw_relatives))

# (c) Reykjavik friend (city 4) between day 8 and day 9 (i.e. indices 7 and 8)
reykjavik_friend = [inCityOnDay(d, 4) for d in [7, 8]]
s.add(Or(reykjavik_friend))

# (No explicit event for Madrid, Split, or Budapest beyond required days)

# Solve the model.
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