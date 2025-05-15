from z3 import *

# City indices and names:
# 0: Seville   (2 days)
# 1: Stuttgart (7 days; events: conference on day 7 and day 13)
# 2: Porto     (3 days)
# 3: Madrid    (4 days; event: visit relatives in Madrid between day 1 and day 4)
city_names = ["Seville", "Stuttgart", "Porto", "Madrid"]
req = [2, 7, 3, 4]  # required day contributions per city

# Total required contributions = 2 + 7 + 3 + 4 = 16.
# We have 13 base days. Since if a flight is taken on a day it counts for both departure and arrival, 
# total_contrib = base days + (#flights).
# So #flights must be 16 - 13 = 3. This means the trip is divided into 4 segments (one per city).

DAYS = 13  # Base days: 0..12 represent day 1 to day 13.

# Allowed direct flights (bidirectional):
# Porto and Stuttgart       => (2,1) and (1,2)
# Seville and Porto         => (0,2) and (2,0)
# Madrid and Porto          => (3,2) and (2,3)
# Madrid and Seville        => (3,0) and (0,3)
allowed_flights = [
    (2, 1), (1, 2),
    (0, 2), (2, 0),
    (3, 2), (2, 3),
    (3, 0), (0, 3)
]

# Create Z3 variables:
# c[d] is the base city for day d.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is True if a flight is taken on day d (for d>=1).
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d starts a new segment.
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Each day, the base city must be one of 0..3.
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < 4)

# 2. Day 0 is always the start of a segment.
s.add(isSeg[0] == True)

# 3. For days 1 to 12, set flight and segment conditions.
for d in range(1, DAYS):
    # A flight occurs if the city changes from the previous day.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight occurs on day d, the flight must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. There must be exactly 3 flights.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 3)

# 5. Enforce that the start of each segment (day 0 and any day with a flight) corresponds to a unique city.
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally, enforce that every city gets visited.
for city in range(4):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# 6. Compute day contributions for each city.
# On day 0, the city c[0] gets 1.
# For each day d>=1:
#   if a flight occurs then both the departure (c[d-1]) and arrival (c[d]) get 1 each,
#   otherwise only the day's city c[d] gets 1.
counts = [Int(f"count_{city}") for city in range(4)]
for city in range(4):
    init = If(c[0] == city, 1, 0)
    daily = []
    for d in range(1, DAYS):
        daily.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == init + Sum(daily))
    s.add(counts[city] == req[city])

# Helper: inCityOnDay(d, target)
# Returns a condition for day d "including" the target city.
# On day 0 it's simply c[0] == target.
# For d>=1, if flight occurs on day d then both departure (c[d-1]) and arrival (c[d]) count.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Add event constraints.
# Event A: Conference in Stuttgart (city 1) on day 7 and day 13.
# (day 7 -> index 6, day 13 -> index 12)
s.add(inCityOnDay(6, 1))
s.add(inCityOnDay(12, 1))

# Event B: Visit relatives in Madrid (city 3) between day 1 and day 4.
# Days 1 to 4 correspond to indices 0 to 3.
madrid_event = [inCityOnDay(d, 3) for d in range(0, 4)]
s.add(Or(madrid_event))

# Solve and output the itinerary.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city = m[c[d]].as_long()
        day_output = f"Day {d+1:2d}: {city_names[city]}"
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[city]
            day_output += f" (Flight: {dep} -> {arr})"
        print(day_output)
    print("\nCity day contributions:")
    for i in range(4):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")