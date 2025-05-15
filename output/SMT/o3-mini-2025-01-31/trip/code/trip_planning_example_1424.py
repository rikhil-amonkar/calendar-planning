from z3 import *

# Cities indices and names:
# 0: Warsaw, 1: Porto, 2: Naples, 3: Brussels, 4: Split,
# 5: Reykjavik, 6: Amsterdam, 7: Lyon, 8: Helsinki, 9: Valencia
city_names = ["Warsaw", "Porto", "Naples", "Brussels", "Split",
              "Reykjavik", "Amsterdam", "Lyon", "Helsinki", "Valencia"]

# Required day counts in each city:
# Warsaw:3, Porto:5, Naples:4, Brussels:3, Split:3,
# Reykjavik:5, Amsterdam:4, Lyon:3, Helsinki:4, Valencia:2.
req = [3, 5, 4, 3, 3, 5, 4, 3, 4, 2]

# Allowed direct flights (as unordered pairs, made bidirectional)
direct_flights = [
    (6, 0),   # Amsterdam - Warsaw
    (8, 3),   # Helsinki - Brussels
    (8, 0),   # Helsinki - Warsaw
    (5, 3),   # Reykjavik - Brussels
    (6, 7),   # Amsterdam - Lyon
    (6, 2),   # Amsterdam - Naples
    (6, 5),   # Amsterdam - Reykjavik
    (2, 9),   # Naples - Valencia
    (1, 3),   # Porto - Brussels
    (6, 4),   # Amsterdam - Split
    (7, 4),   # Lyon - Split
    (0, 4),   # Warsaw - Split
    (1, 6),   # Porto - Amsterdam
    (8, 4),   # Helsinki - Split
    (3, 7),   # Brussels - Lyon
    (1, 7),   # Porto - Lyon
    (5, 0),   # Reykjavik - Warsaw
    (3, 9),   # Brussels - Valencia
    (9, 7),   # Valencia - Lyon
    (1, 0),   # Porto - Warsaw
    (0, 9),   # Warsaw - Valencia
    (6, 8),   # Amsterdam - Helsinki
    (1, 9),   # Porto - Valencia
    (0, 3),   # Warsaw - Brussels
    (0, 2),   # Warsaw - Naples
    (2, 4),   # Naples - Split
    (8, 2),   # Helsinki - Naples
    (8, 5),   # Helsinki - Reykjavik
    (6, 9),   # Amsterdam - Valencia
    (2, 3)    # Naples - Brussels
]

# Make allowed flights bidirectional:
allowed_flights = []
for (a, b) in direct_flights:
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# Number of itinerary days:
DAYS = 27

# Create Z3 variables:
# c[d] (for d=0..DAYS-1) is the "base city" on day d+1.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is True if on day d (d>=1) a flight occurs,
# i.e. when c[d] ≠ c[d-1]. (Day0 has no flight.)
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] is True if day d is the start of a segment, i.e.
# day0 always, and every day when a flight occurs.
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Every c[d] is one of the 10 cities:
for d in range(DAYS):
    s.add(And(c[d] >= 0, c[d] < 10))

# No fixed start was prescribed, so we leave c[0] free.
# But day0 is always a segment start:
s.add(isSeg[0] == True)

# For days 1..DAYS-1:
for d in range(1, DAYS):
    # flight[d] holds exactly when there is a change of city:
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    # When a flight happens, the transition must be allowed.
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 )
         )

# We plan to visit 10 cities, so there must be exactly 9 flights,
# which gives 10 segments (day0 + flight days).
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 9)

# The 10 different visited cities (the segment–start cities)
# must be distinct.
for d1 in range(DAYS):
    for d2 in range(d1+1, DAYS):
        s.add(Implies(And(isSeg[d1], isSeg[d2]), c[d1] != c[d2]))

# (Optional) Ensure every city appears in some day – not strictly needed since
# we force 10 distinct segments.
for city in range(10):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Now count the “day contributions”. On day0 (day1) we contribute 1 for c[0].
# For each later day d (d>=1): 
#    if flight[d] then contribute 1 for c[d-1] and 1 for c[d];
#    otherwise, add 1 for c[d].
counts = [Int(f"count_{city}") for city in range(10)]
for city in range(10):
    day0 = If(c[0] == city, 1, 0)
    contribs = []
    for d in range(1, DAYS):
        contrib = If(flight[d],
                     If(c[d] == city, 1, 0) + If(c[d-1] == city, 1, 0),
                     If(c[d] == city, 1, 0))
        contribs.append(contrib)
    s.add(counts[city] == day0 + Sum(contribs))
    s.add(counts[city] == req[city])

# Helper function to state that on day d (d>=0) the plan “includes” a given city.
# (On a flight day the traveler is present in both c[d-1] and c[d].)
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    else:
        return If(flight[d],
                  Or(c[d-1] == target, c[d] == target),
                  c[d] == target)

# Constraint: Workshop in Porto (city 1) between day1 and day5 (d = 0..4) 
ws_porto = [inCityOnDay(d, 1) for d in range(0, 5)]
s.add(Or(ws_porto))

# Constraint: In Naples (city 2) on day 17 and day 20.
# That is d=16 and d=19 respectively.
s.add(inCityOnDay(16, 2))
s.add(inCityOnDay(19, 2))

# Constraint: Annual show in Brussels (city 3) between day20 and day22 (d = 19..21).
show_brussels = [inCityOnDay(d, 3) for d in range(19, 22)]
s.add(Or(show_brussels))

# Constraint: Relatives meeting in Amsterdam (city 6) between day5 and day8 (d = 4..7).
rel_amsterdam = [inCityOnDay(d, 6) for d in range(4, 8)]
s.add(Or(rel_amsterdam))

# Constraint: Wedding in Helsinki (city 8) between day8 and day11 (d = 7..10).
wed_helsinki = [inCityOnDay(d, 8) for d in range(7, 11)]
s.add(Or(wed_helsinki))

# If the model is sat, print the itinerary with day contributions.
if s.check() == sat:
    m = s.model()
    itinerary = []
    for d in range(DAYS):
        info = {}
        info["day"] = d+1
        info["base"] = city_names[m[c[d]].as_long()]
        # if a flight occurs on day d (and d>=1) record the flight details.
        if d >= 1 and m.evaluate(flight[d]):
            info["flight_from"] = city_names[m[c[d-1]].as_long()]
            info["flight_to"] = city_names[m[c[d]].as_long()]
        itinerary.append(info)
        
    print("Found a valid itinerary:")
    for info in itinerary:
        if "flight_from" in info:
            print("Day {:2d}: Flight day – departing {} and arriving {}."
                  .format(info["day"], info["flight_from"], info["base"]))
        else:
            print("Day {:2d}: Stay in {}.".format(info["day"], info["base"]))
    
    print("\nCity day counts:")
    for city in range(10):
        print(f"{city_names[city]}: {m.evaluate(counts[city])}")
else:
    print("No solution found")