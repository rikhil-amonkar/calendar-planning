from z3 import *

# We have 5 cities with the following requirements:
# 0: Istanbul   – 2 days; event: visit relatives in Istanbul between day 6 and day 7.
# 1: Rome       – 3 days.
# 2: Seville    – 4 days.
# 3: Naples     – 7 days.
# 4: Santorini  – 4 days; event: attend wedding in Santorini between day 13 and day 16.
city_names = ["Istanbul", "Rome", "Seville", "Naples", "Santorini"]
req = [2, 3, 4, 7, 4]  # required day contributions per city

# Total contributions required = 2+3+4+7+4 = 20.
# Total base days = 16. Since flight days add an extra contribution (departure and arrival),
# we need 20 - 16 = 4 flights. This partitions the itinerary into 5 segments (one per city).

DAYS = 16  # Days indices: 0 ... 15 correspond to day 1...16

# Allowed direct flights (bidirectional, unless specified as one-way):
# Rome and Santorini       -> (Rome, Santorini) and (Santorini, Rome): (1,4) and (4,1)
# Seville and Rome         -> (Seville, Rome) and (Rome, Seville):         (2,1) and (1,2)
# Istanbul and Naples      -> (Istanbul, Naples) and (Naples, Istanbul):     (0,3) and (3,0)
# Naples and Santorini     -> (Naples, Santorini) and (Santorini, Naples):   (3,4) and (4,3)
# Rome and Naples          -> (Rome, Naples) and (Naples, Rome):             (1,3) and (3,1)
# Rome and Istanbul        -> (Rome, Istanbul) and (Istanbul, Rome):         (1,0) and (0,1)
allowed_flights = [
    (1,4), (4,1),
    (2,1), (1,2),
    (0,3), (3,0),
    (3,4), (4,3),
    (1,3), (3,1),
    (1,0), (0,1)
]

# Create Z3 variables:
# c[d] : base city on day d (0 <= d < DAYS)
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] : whether a flight occurs on day d (for d>=1; day0 is the beginning of a segment)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] : whether day d is the start of a new segment (day0 always true; later if a flight occurs)
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# 1. Domain: each c[d] is in {0,...,4}
for d in range(DAYS):
    s.add(c[d] >= 0, c[d] < len(city_names))

# 2. Day0 is always a segment start.
s.add(isSeg[0] == True)

# 3. For days 1 to 15, set up flight conditions and segment markers.
for d in range(1, DAYS):
    # flight occurs if current day's city differs from previous day's city.
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # If a flight happens on day d, then the connection must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 ))

# 4. Exactly 4 flights must occur.
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 4)

# 5. Ensure that the starting city of each segment is unique (each city is visited exactly once).
for i in range(DAYS):
    for j in range(i+1, DAYS):
        s.add(Implies(And(isSeg[i], isSeg[j]), c[i] != c[j]))

# Optionally, enforce that each city appears somewhere in the itinerary.
for city in range(len(city_names)):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# 6. Compute the day contributions for each city.
# Day 0 contributes 1 for city c[0].
# For each day d>=1:
#   If a flight occurs on day d, then add 1 for departure (c[d-1]) and 1 for arrival (c[d]).
#   If no flight occurs, add 1 for c[d] only.
counts = [Int(f"count_{city}") for city in range(len(city_names))]
for city in range(len(city_names)):
    init = If(c[0] == city, 1, 0)
    day_contribs = []
    for d in range(1, DAYS):
        day_contribs.append(
            If(flight[d],
               If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
               If(c[d] == city, 1, 0)
            )
        )
    s.add(counts[city] == init + Sum(day_contribs))
    s.add(counts[city] == req[city])

# Helper function: inCityOnDay
# Returns a condition representing that the itinerary "includes" a target city on day d.
# On a flight day, both the departure and arrival count.
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# 7. Event Constraints:
# (a) In Istanbul (city 0), visit relatives between day 6 and day 7.
#    Days 6 and 7 correspond to indices 5 and 6.
istanbul_event = [inCityOnDay(d, 0) for d in [5, 6]]
s.add(Or(istanbul_event))

# (b) Attend a wedding in Santorini (city 4) between day 13 and day 16.
#    Days 13, 14, 15, 16 correspond to indices 12, 13, 14, 15.
santorini_event = [inCityOnDay(d, 4) for d in range(12, 16)]
s.add(Or(santorini_event))

# Solve and print the itinerary if found.
if s.check() == sat:
    m = s.model()
    print("Found a valid itinerary:")
    for d in range(DAYS):
        city_index = m[c[d]].as_long()
        day_info = f"Day {d+1:2d}: {city_names[city_index]}"
        # If a flight occurs on this day (d>=1), print flight details.
        if d >= 1 and m.evaluate(flight[d]):
            dep = city_names[m[c[d-1]].as_long()]
            arr = city_names[city_index]
            day_info += f" (Flight: {dep} -> {arr})"
        print(day_info)
    print("\nCity day contributions:")
    for i in range(len(city_names)):
        print(f"{city_names[i]}: {m.evaluate(counts[i])}")
else:
    print("No solution found")