from z3 import *

# We use the following encoding:
#
# We have 7 visited cities (segments) with fixed “durations” (in days):
#   Porto:      2 days
#   Geneva:     3 days
#   Mykonos:    3 days
#   Manchester: 4 days
#   Hamburg:    5 days
#   Naples:     5 days
#   Frankfurt:  2 days
#
# When you “fly” from one city (segment) to the next,
# the flight day is counted as a day in both cities.
# Hence, the sum of segment durations is 24 but the overall unique days is 24 – 6 = 18.
#
# For a sequence of segments i = 0..6 let s[i] be the starting day of segment i.
# We fix s[0] = 1 and require that for i>=1:
#    s[i] = s[i-1] + (duration(city[i-1]) - 1)
# Then the finish day for segment i is: f[i] = s[i] + duration(city[i]) - 1.
# The last finish day f[6] is forced to equal 18.
#
# Besides the totals, we include extra constraints:
#
# 1. If the segment is Frankfurt then, to attend the annual show (days 5–6)
#    and since Frankfurt’s duration is 2 it must appear with s = 5.
#
# 2. If the segment is Mykonos then its interval [s, s+2] must
#    have a nonempty intersection with [10,12] (i.e. friend meeting).
#
# 3. If the segment is Manchester then its interval [s, s+3] must intersect [15,18] (wedding).
#
# Also, we require that consecutive cities in the order are connected by a direct flight.
#
# We label the cities by integers as follows:
#   0: Porto
#   1: Geneva
#   2: Mykonos
#   3: Manchester
#   4: Hamburg
#   5: Naples
#   6: Frankfurt
#
# Direct flight connections – note: most pairs are bidirectional
# except one which is given as "from Hamburg to Geneva":
#
# Bidirectional pairs:
#   (Hamburg, Frankfurt) and (Frankfurt, Hamburg)
#   (Naples, Mykonos) and (Mykonos, Naples)
#   (Hamburg, Porto) and (Porto, Hamburg)
#   (Mykonos, Geneva) and (Geneva, Mykonos)
#   (Frankfurt, Geneva) and (Geneva, Frankfurt)
#   (Frankfurt, Porto) and (Porto, Frankfurt)
#   (Geneva, Porto) and (Porto, Geneva)
#   (Geneva, Manchester) and (Manchester, Geneva)
#   (Naples, Manchester) and (Manchester, Naples)
#   (Frankfurt, Naples) and (Naples, Frankfurt)
#   (Frankfurt, Manchester) and (Manchester, Frankfurt)
#   (Naples, Geneva) and (Geneva, Naples)
#   (Porto, Manchester) and (Manchester, Porto)
#   (Hamburg, Manchester) and (Manchester, Hamburg)
#
# One directional pair:
#   (Hamburg, Geneva) is allowed (but not Geneva -> Hamburg).
#
# We now encode the problem in Z3.

# Mapping: city_id -> duration and city name.
durations = {0: 2, 1: 3, 2: 3, 3: 4, 4: 5, 5: 5, 6: 2}
city_names = {0: "Porto", 1: "Geneva", 2: "Mykonos", 3: "Manchester", 4: "Hamburg", 5: "Naples", 6: "Frankfurt"}

# Allowed flight pairs (tuples): (from, to)
allowed_flights = [
    (4, 6), (6, 4),           # Hamburg <-> Frankfurt
    (5, 2), (2, 5),           # Naples <-> Mykonos
    (4, 0), (0, 4),           # Hamburg <-> Porto
    (2, 1), (1, 2),           # Mykonos <-> Geneva
    (6, 1), (1, 6),           # Frankfurt <-> Geneva
    (6, 0), (0, 6),           # Frankfurt <-> Porto
    (1, 0), (0, 1),           # Geneva <-> Porto
    (1, 3), (3, 1),           # Geneva <-> Manchester
    (5, 3), (3, 5),           # Naples <-> Manchester
    (6, 5), (5, 6),           # Frankfurt <-> Naples
    (6, 3), (3, 6),           # Frankfurt <-> Manchester
    (5, 1), (1, 5),           # Naples <-> Geneva
    (0, 3), (3, 0),           # Porto <-> Manchester
    (4, 3), (3, 4),           # Hamburg <-> Manchester
    (4, 1)                   # Hamburg -> Geneva (one directional)
]

# Create Z3 solver.
solver = Solver()

# Create 7 integer variables for the ordered cities (indices 0..6).
cities = [Int(f"city_{i}") for i in range(7)]
# Their values must be in 0..6 and all distinct.
for i in range(7):
    solver.add(cities[i] >= 0, cities[i] <= 6)
solver.add(Distinct(cities))

# Create 7 integer variables for the starting day of each segment.
s = [Int(f"s_{i}") for i in range(7)]
solver.add(s[0] == 1)  # The trip starts on day 1

# For convenience, define a function (as a Z3 if-chain) that returns the duration for a given city variable.
def duration(city_var):
    return If(city_var == 0, durations[0],
           If(city_var == 1, durations[1],
           If(city_var == 2, durations[2],
           If(city_var == 3, durations[3],
           If(city_var == 4, durations[4],
           If(city_var == 5, durations[5],
              durations[6]))))))

# Chain the start times: for each segment i>=1, 
# s[i] = s[i-1] + duration(city[i-1]) - 1 
# (because the flight day is counted in both segments).
for i in range(1, 7):
    solver.add(s[i] == s[i-1] + duration(cities[i-1]) - 1)

# The finish day of segment i is f[i] = s[i] + duration(city[i]) - 1.
# In particular, we require that the finish day of the last segment is 18.
solver.add(s[6] + duration(cities[6]) - 1 == 18)

# For each flight from segment i to segment i+1, require that the ordered pair (cities[i], cities[i+1]) is allowed.
for i in range(6):
    allowed_transition = []
    for (frm, to) in allowed_flights:
        allowed_transition.append(And(cities[i] == frm, cities[i+1] == to))
    solver.add(Or(allowed_transition))

# Add event and timing constraints:
for i in range(7):
    # Compute finish day for segment i.
    finish_i = s[i] + duration(cities[i]) - 1

    # 1. If visiting Mykonos (city id 2) then the stay [s, finish] must overlap days 10–12.
    #    (i.e. s[i] <= 12 and finish_i >= 10)
    solver.add(Or(cities[i] != 2, And(s[i] <= 12, finish_i >= 10)))
    
    # 2. If visiting Manchester (city id 3) then the stay must include a day in [15,18]
    #    (i.e. s[i] <= 18 and finish_i >= 15)
    solver.add(Or(cities[i] != 3, And(s[i] <= 18, finish_i >= 15)))
    
    # 3. To attend the Frankfurt show (days 5–6) and since Frankfurt is 2 days long,
    #    if visiting Frankfurt (city id 6) then its start must be day 5.
    solver.add(Or(cities[i] != 6, s[i] == 5))

# Try to solve
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    # Build an itinerary as a list of segments.
    # For each segment, output its city (by name), its start day and its finish day.
    for i in range(7):
        city_val = model[cities[i]].as_long()
        s_val = model[s[i]].as_long()
        d_val = durations[city_val]
        f_val = s_val + d_val - 1
        itinerary.append({
            "city": city_names[city_val],
            "start_day": s_val,
            "end_day": f_val
        })
    # Output the result (JSON-formatted dictionary).
    import json
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found")