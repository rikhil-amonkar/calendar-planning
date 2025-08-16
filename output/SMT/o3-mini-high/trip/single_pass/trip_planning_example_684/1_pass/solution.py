from z3 import *
import json

# We map cities to indices:
# 0: Amsterdam (stay 4 days; must see relatives between day 5 and 8)
# 1: Edinburgh (stay 5 days)
# 2: Brussels (stay 5 days)
# 3: Vienna (stay 5 days)
# 4: Berlin (stay 4 days; must meet friend between day 16 and 19)
# 5: Reykjavik (stay 5 days; must attend workshop between day 12 and 16)

# Allowed direct flight connections (bidirectional):
# Edinburgh – Berlin
# Amsterdam – Berlin
# Edinburgh – Amsterdam
# Vienna – Berlin
# Berlin – Brussels
# Vienna – Reykjavik
# Edinburgh – Brussels
# Vienna – Brussels
# Amsterdam – Reykjavik
# Reykjavik – Brussels
# Amsterdam – Vienna
# Reykjavik – Berlin
allowed_pairs = [
    (1,4), (4,1),
    (0,4), (4,0),
    (1,0), (0,1),
    (3,4), (4,3),
    (4,2), (2,4),
    (3,5), (5,3),
    (1,2), (2,1),
    (3,2), (2,3),
    (0,5), (5,0),
    (0,3), (3,0),
    (5,2), (2,5),
    (5,4), (4,5)
]

# Durations for each city:
durations = {0: 4, 1: 5, 2: 5, 3: 5, 4: 4, 5: 5}
city_names = {0: "Amsterdam", 1: "Edinburgh", 2: "Brussels", 
              3: "Vienna", 4: "Berlin", 5: "Reykjavik"}

# We have 6 city segments. We use two sets of variables:
#  - 'order[i]' will be an integer in 0..5 specifying which city is visited in segment i.
#    They must form a permutation.
#  - 's[i]' will be the start day of segment i.
# By our rules, if you fly from segment i to i+1,
# day s[i+1] is the flight day and is counted both in the tail of segment i and the beginning of segment i+1.
# Hence the number of days you spend in segment i is:
#    [s[i], s[i] + durations[order[i]] - 1]
# And the overall itinerary lasts from day 1 to day (s[5] + durations[order[5]] - 1).
# We require the overall itinerary to be exactly 23 days when not double-counting flight days.
# (Because the sum of durations is 28, and there are 5 overlapping flight days: 28-5 = 23.)

s = [Int(f"s{i}") for i in range(6)]
order = [Int(f"order{i}") for i in range(6)]

solver = Solver()

# Each segment's city must be one of 0..5 and the segments must be all different.
for i in range(6):
    solver.add(order[i] >= 0, order[i] <= 5)
solver.add(Distinct(order))

# The first segment starts at day 1.
solver.add(s[0] == 1)

# Helper: given a city variable (an Int), return its duration as an IntExpr.
def dur(city):
    return If(city == 0, 4,
           If(city == 1, 5,
           If(city == 2, 5,
           If(city == 3, 5,
           If(city == 4, 4,
           5)))))

# Relate start days with durations.
# For i >= 1, segment i starts on the same day that segment i-1 ends.
# The end of segment i-1 is: s[i-1] + dur(order[i-1]) - 1.
for i in range(1, 6):
    solver.add(s[i] == s[i-1] + dur(order[i-1]) - 1)

# Overall itinerary: the last segment ends on day 23.
solver.add(s[5] + dur(order[5]) - 1 == 23)

# Flight connectivity: for each consecutive pair of segments, the cities must be connected.
for i in range(5):
    allowed_conns = []
    for (a, b) in allowed_pairs:
        allowed_conns.append(And(order[i] == a, order[i+1] == b))
    solver.add(Or(allowed_conns))

# Special scheduling constraints:
# 1. Relatives in Amsterdam: if Amsterdam (0) is visited in a segment,
#    the period of that segment [s, s+4-1] must intersect days 5..8.
for i in range(6):
    solver.add(Implies(order[i] == 0, And(s[i] <= 8, s[i] + 4 - 1 >= 5)))

# 2. Meet a friend in Berlin: if Berlin (4) is visited,
#    its days [s, s+4-1] must intersect days 16..19.
for i in range(6):
    solver.add(Implies(order[i] == 4, And(s[i] <= 19, s[i] + 4 - 1 >= 16)))

# 3. Attend a workshop in Reykjavik: if Reykjavik (5) is visited,
#    its days [s, s+5-1] must intersect days 12..16.
for i in range(6):
    solver.add(Implies(order[i] == 5, And(s[i] <= 16, s[i] + 5 - 1 >= 12)))

# Check for a solution.
if solver.check() == sat:
    model = solver.model()
    # Collect the segments as a list of tuples: (city_name, start_day, end_day)
    segments = []
    for i in range(6):
        city_id = model.evaluate(order[i]).as_long()
        s_day = model.evaluate(s[i]).as_long()
        d = durations[city_id]
        e_day = s_day + d - 1
        segments.append((city_names[city_id], s_day, e_day))
    
    # For clarity, sort the segments by start day (they are in time order already)
    # Build the final day-by-day itinerary.
    # IMPORTANT: On a flight day (when segments overlap), that day counts for both cities.
    itinerary = []
    # We know days run from 1 to 23.
    for day in range(1, 24):
        day_cities = []
        for (name, start_day, end_day) in segments:
            if day >= start_day and day <= end_day:
                day_cities.append(name)
        # If only one city is active that day, we output it as a string.
        # If two cities are active (i.e. the flight day), output them as a list.
        if len(day_cities) == 1:
            mapping = {"day": day, "city": day_cities[0]}
        else:
            mapping = {"day": day, "city": day_cities}
        itinerary.append(mapping)
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")