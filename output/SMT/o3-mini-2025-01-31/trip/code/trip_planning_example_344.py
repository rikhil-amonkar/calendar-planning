from z3 import *

# Cities indexed as follows:
# 0: Valencia, 1: Athens, 2: Naples, 3: Zurich
city_names = ["Valencia", "Athens", "Naples", "Zurich"]

# Required number of days in each city:
# Valencia: 6, Athens: 6, Naples: 5, Zurich: 6.
req = [6, 6, 5, 6]

# Allowed flights.
# Explanation:
# - "Valencia and Naples": allow (0,2) and (2,0)
# - "from Valencia to Athens": allow only (0,1)
# - "Athens and Naples": allow (1,2) and (2,1)
# - "Zurich and Naples": allow (3,2) and (2,3)
# - "Athens and Zurich": allow (1,3) and (3,1)
# - "Zurich and Valencia": allow (3,0) and (0,3)
allowed_flights = [
    (0,2), (2,0),
    (0,1),              # only from Valencia to Athens
    (1,2), (2,1),
    (3,2), (2,3),
    (1,3), (3,1),
    (3,0), (0,3)
]

# Total number of itinerary days.
DAYS = 20

# Create Z3 variables.
# c[d] (for d=0..DAYS-1) is the “base city” on day d+1.
c = [Int(f"c_{d}") for d in range(DAYS)]
# flight[d] is a Boolean that is True on day d (for d>=1) if a flight occurs,
# i.e. when the base city changes from the previous day.
flight = [Bool(f"flight_{d}") for d in range(DAYS)]
# isSeg[d] indicates that day d is the beginning of a new segment: day 0 always and
# every day when a flight occurs.
isSeg = [Bool(f"seg_{d}") for d in range(DAYS)]

s = Solver()

# Each day’s base city must be one of the 4.
for d in range(DAYS):
    s.add(And(c[d] >= 0, c[d] < 4))

# Day 0 is automatically a segment start.
s.add(isSeg[0] == True)

# For days 1 to DAYS-1, define the flight indicator and ensure that if a flight occurs,
# then the pair (previous city, current city) is an allowed flight.
for d in range(1, DAYS):
    s.add(flight[d] == (c[d] != c[d-1]))
    s.add(isSeg[d] == flight[d])
    s.add(Implies(flight[d],
                  Or([And(c[d-1] == frm, c[d] == to) for (frm, to) in allowed_flights])
                 )
         )

# Exactly 3 flights must occur so that the extra count is 3 (total day count becomes 20+3 = 23).
s.add(Sum([If(flight[d], 1, 0) for d in range(1, DAYS)]) == 3)

# The 4 segments (starting day 0 and every flight day) must correspond to 4 distinct cities.
for d1 in range(DAYS):
    for d2 in range(d1+1, DAYS):
        s.add(Implies(And(isSeg[d1], isSeg[d2]), c[d1] != c[d2]))

# Optionally, you could enforce that each city appears in some day.
for city in range(4):
    s.add(Or([c[d] == city for d in range(DAYS)]))

# Compute the “day contribution” count for each city.
# The idea is:
#  - On day 0, the traveler is in city c[0] (counts 1 for that city).
#  - For each subsequent day d (1<=d<=DAYS-1):
#       If flight occurs on day d, then both the previous city and c[d] get one count.
#       Otherwise, only c[d] gets one count.
counts = [Int(f"count_{city}") for city in range(4)]
for city in range(4):
    day0 = If(c[0] == city, 1, 0)
    contribs = []
    for d in range(1, DAYS):
        contrib = If(flight[d],
                     If(c[d-1] == city, 1, 0) + If(c[d] == city, 1, 0),
                     If(c[d] == city, 1, 0))
        contribs.append(contrib)
    s.add(counts[city] == day0 + Sum(contribs))
    s.add(counts[city] == req[city])

# Helper function for “inCityOnDay”.
# On day d:
#  - If d=0 then we require c[0] == target.
#  - For d>=1, if a flight occurs then the traveler is in either c[d-1] or c[d],
#    otherwise the traveler is in c[d].
def inCityOnDay(d, target):
    if d == 0:
        return c[0] == target
    return If(flight[d],
              Or(c[d-1] == target, c[d] == target),
              c[d] == target)

# Additional scheduling constraints:
# 1. Relatives in Athens (city 1) between day 1 and day 6 (i.e. days 1..6, indices 0..5).
relatives_athens = [inCityOnDay(d, 1) for d in range(0, 6)]
s.add(Or(relatives_athens))

# 2. Wedding in Naples (city 2) between day 16 and day 20 (indices 15..19).
wedding_naples = [inCityOnDay(d, 2) for d in range(15, 20)]
s.add(Or(wedding_naples))

# Check the model and print an itinerary if one is found.
if s.check() == sat:
    m = s.model()
    itinerary = []
    for d in range(DAYS):
        day_info = {}
        day_info["day"] = d + 1
        day_info["base"] = city_names[m[c[d]].as_long()]
        if d >= 1 and m.evaluate(flight[d]):
            day_info["flight_from"] = city_names[m[c[d-1]].as_long()]
            day_info["flight_to"] = city_names[m[c[d]].as_long()]
        itinerary.append(day_info)

    print("Found a valid itinerary:")
    for day in itinerary:
        if "flight_from" in day:
            print("Day {:2d}: Flight day – departing {} and arriving {}."
                  .format(day["day"], day["flight_from"], day["base"]))
        else:
            print("Day {:2d}: Stay in {}.".format(day["day"], day["base"]))
    
    print("\nDay counts in each city:")
    for city in range(4):
        print(f"{city_names[city]}: {m.evaluate(counts[city])}")
else:
    print("No solution found")