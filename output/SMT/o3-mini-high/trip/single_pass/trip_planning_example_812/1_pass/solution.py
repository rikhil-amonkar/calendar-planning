from z3 import *
import json

# There are 7 cities.
# We'll use the following integer mapping:
# 0: Paris, 1: Florence, 2: Vienna, 3: Porto, 4: Munich, 5: Nice, 6: Warsaw
city_names = {0: "Paris", 1: "Florence", 2: "Vienna", 3: "Porto", 4: "Munich", 5: "Nice", 6: "Warsaw"}
# Required durations for each city (number of days “spent” in that city)
# Note: When flying from one city to the next on the flight day, that day is counted
# in both cities. Thus the sum of required days is 26, and with 6 flights the total itinerary is 26-6=20 days.
durations = {0: 5, 1: 3, 2: 2, 3: 3, 4: 5, 5: 5, 6: 3}

# Helper: given a Z3 integer x representing a city, return its duration as a Z3 expression.
def dur(x):
    return If(x == 0, 5,
           If(x == 1, 3,
           If(x == 2, 2,
           If(x == 3, 3,
           If(x == 4, 5,
           If(x == 5, 5, 3))))))

# Define allowed flight transitions between two cities.
# IMPORTANT: note that almost all pairs are bidirectional except the "from Florence to Munich"
# which is only allowed if departing from Florence.
def allowed(a, b):
    return Or(
      # Paris <> Warsaw
      And(a == 0, b == 6), And(a == 6, b == 0),
      # Paris <> Florence (bidirectional)
      And(a == 0, b == 1), And(a == 1, b == 0),
      # Paris <> Vienna
      And(a == 0, b == 2), And(a == 2, b == 0),
      # Paris <> Nice
      And(a == 0, b == 5), And(a == 5, b == 0),
      # Paris <> Munich
      And(a == 0, b == 4), And(a == 4, b == 0),
      # Porto <> Vienna
      And(a == 3, b == 2), And(a == 2, b == 3),
      # Porto <> Munich
      And(a == 3, b == 4), And(a == 4, b == 3),
      # Porto <> Nice
      And(a == 3, b == 5), And(a == 5, b == 3),
      # Porto <> Paris
      And(a == 3, b == 0), And(a == 0, b == 3),
      # Porto <> Warsaw
      And(a == 3, b == 6), And(a == 6, b == 3),
      # Florence <> Vienna
      And(a == 1, b == 2), And(a == 2, b == 1),
      # "from Florence to Munich" is allowed (but NOT reverse!)
      And(a == 1, b == 4),
      # Munich <> Vienna
      And(a == 4, b == 2), And(a == 2, b == 4),
      # Munich <> Warsaw
      And(a == 4, b == 6), And(a == 6, b == 4),
      # Munich <> Nice
      And(a == 4, b == 5), And(a == 5, b == 4),
      # Warsaw <> Vienna
      And(a == 6, b == 2), And(a == 2, b == 6),
      # Warsaw <> Nice
      And(a == 6, b == 5), And(a == 5, b == 6)
    )

# We must choose an ordering (a permutation) of the 7 cities.
# Create 7 Int variables for the city order: p[0] ... p[6]
p_vars = [Int(f"p{i}") for i in range(7)]
# Also create integer variables s0 ... s6 to mark the start day of each segment.
s_vars = [Int(f"s{i}") for i in range(7)]
# Create a solver instance
solver = Solver()

# p_vars must all be in the range 0..6 and all different:
for p in p_vars:
    solver.add(p >= 0, p <= 6)
solver.add(Distinct(p_vars))

# Define the schedule. The itinerary is split into 7 segments.
# The rule is:
#   s0 = 1.
#   For i > 0, s[i] = 1 + sum_{j=0}^{i-1}( dur(p[j]) - 1 ).
# And the last segment must end on day 20:
#   s6 + dur(p_vars[6]) - 1 = 20.
solver.add(s_vars[0] == 1)
solver.add(s_vars[1] == dur(p_vars[0])) 
solver.add(s_vars[2] == dur(p_vars[0]) + dur(p_vars[1]) - 1)
solver.add(s_vars[3] == dur(p_vars[0]) + dur(p_vars[1]) + dur(p_vars[2]) - 2)
solver.add(s_vars[4] == dur(p_vars[0]) + dur(p_vars[1]) + dur(p_vars[2]) + dur(p_vars[3]) - 3)
solver.add(s_vars[5] == dur(p_vars[0]) + dur(p_vars[1]) + dur(p_vars[2]) + dur(p_vars[3]) + dur(p_vars[4]) - 4)
solver.add(s_vars[6] == dur(p_vars[0]) + dur(p_vars[1]) + dur(p_vars[2]) + dur(p_vars[3]) + dur(p_vars[4]) + dur(p_vars[5]) - 5)
solver.add(s_vars[6] + dur(p_vars[6]) - 1 == 20)

# The flight transitions: between successive segments, there is a direct flight.
# When flying on day s_vars[i] (i>=1) you are in BOTH the previous city and the new one.
for i in range(6):
    solver.add(allowed(p_vars[i], p_vars[i+1]))

# Add special event constraints:
# 1. Workshop in Porto (city 3) must take place between day 1 and 3.
#    This means that if a segment i is in Porto then its segment must intersect days 1-3,
#    i.e. its start day s_vars[i] must be ≤ 3.
for i in range(7):
    solver.add(Implies(p_vars[i] == 3, s_vars[i] <= 3))

# 2. Wedding in Warsaw (city 6) between day 13 and 15.
#    For a segment with Warsaw (duration 3 => covers days s to s+2), the interval [s, s+2]
#    must intersect [13,15]. A sufficient constraint is: s_vars[i] >= 11 and s_vars[i] <= 15.
for i in range(7):
    solver.add(Implies(p_vars[i] == 6, And(s_vars[i] >= 11, s_vars[i] <= 15)))

# 3. Relatives in Vienna (city 2) between day 19 and 20.
#    For Vienna (duration 2, covering [s, s+1]), we need s_vars[i] >= 18 and s_vars[i] <= 19.
for i in range(7):
    solver.add(Implies(p_vars[i] == 2, And(s_vars[i] >= 18, s_vars[i] <= 19)))

# Optionally, you might fix Vienna to be the very last city, though it will be forced by the day‐constraints.
# Uncomment the next line if you wish to force Vienna to be last.
# solver.add(p_vars[6] == 2)

# Check for a solution and extract one if it exists.
if solver.check() == sat:
    m = solver.model()
    order = [m.evaluate(p_vars[i]).as_long() for i in range(7)]
    starts = [m.evaluate(s_vars[i]).as_long() for i in range(7)]
    # Compute the interval for each city segment: it covers days [s, s + duration - 1]
    segments = []
    for i in range(7):
        city = order[i]
        seg_start = starts[i]
        seg_duration = durations[city]
        seg_end = seg_start + seg_duration - 1
        segments.append((city, seg_start, seg_end))
    
    # Now, build the day-by-day itinerary for days 1 to 20.
    # On a flight day (which is the start day of a segment for i>=1), the day counts in both the previous segment and the current one.
    itinerary = []
    for d in range(1, 21):
        cities_today = []
        for (city, s_day, e_day) in segments:
            if s_day <= d <= e_day:
                cities_today.append(city_names[city])
        # If two cities are present, join them with a '/'
        if len(cities_today) == 1:
            day_entry = cities_today[0]
        else:
            day_entry = "/".join(cities_today)
        itinerary.append({"day": d, "city": day_entry})
    
    # Output the result as a JSON dictionary.
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")