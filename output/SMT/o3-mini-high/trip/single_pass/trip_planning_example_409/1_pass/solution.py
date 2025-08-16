from z3 import *
import json

# We label the five cities with integers:
# 0: Hamburg    (requires 2 days)
# 1: Zurich     (requires 3 days; also the wedding must be here between day1 and day3)
# 2: Helsinki   (requires 2 days)
# 3: Bucharest  (requires 2 days)
# 4: Split      (requires 7 days; and the conference on day 4 and 10 is in Split)
city_names = {0: "Hamburg", 1: "Zurich", 2: "Helsinki", 3: "Bucharest", 4: "Split"}
required = {0: 2, 1: 3, 2: 2, 3: 2, 4: 7}

# We have 5 segments. For each segment i (0..4) we have an assigned city (seg[i]).
# Also define four "flight days": a1, a2, a3, a4.
# The itinerary is divided as:
#   Segment 0: Days 1 ... a1         [length = a1]
#   Segment 1: Days a1 ... a2        [length = a2 - a1 + 1]
#   Segment 2: Days a2 ... a3        [length = a3 - a2 + 1]
#   Segment 3: Days a3 ... a4        [length = a4 - a3 + 1]
#   Segment 4: Days a4 ... 12        [length = 13 - a4]
#
# And the requirement is that the segment’s length equals the required number
# of days for whichever city is visited in that segment.
#
# Also note: on a flight day the day counts for both the leaving and the arriving city.

# Create the Z3 solver:
s = Solver()

# Define flight day boundaries (integers between 1 and 12).
a1, a2, a3, a4 = Ints('a1 a2 a3 a4')
s.add(a1 >= 1, a2 >= 1, a3 >= 1, a4 >= 1)
s.add(a1 < a2, a2 < a3, a3 < a4, a4 <= 12)

# Define the city assignments for the 5 segments.
seg = [Int(f'seg{i}') for i in range(5)]
for i in range(5):
    s.add(And(seg[i] >= 0, seg[i] <= 4))
s.add(Distinct(seg))  # each city is visited exactly once

# A helper function: given a segment variable (a city index), return its required days.
def get_req(seg_var):
    return If(seg_var == 0, required[0],
           If(seg_var == 1, required[1],
           If(seg_var == 2, required[2],
           If(seg_var == 3, required[3],
              required[4]))))

# Impose the duration constraints for each segment:
# Segment 0: length = a1
s.add(a1 == get_req(seg[0]))
# Segment 1: length = a2 - a1 + 1
s.add(a2 == a1 + get_req(seg[1]) - 1)
# Segment 2: length = a3 - a2 + 1
s.add(a3 == a2 + get_req(seg[2]) - 1)
# Segment 3: length = a4 - a3 + 1
s.add(a4 == a3 + get_req(seg[3]) - 1)
# Segment 4: length = 13 - a4
s.add(13 - a4 == get_req(seg[4]))

# Direct flight (connectivity) information (flights are bidirectional):
# Allowed pairs (from, to) are:
#  (Zurich, Helsinki), (Helsinki, Zurich),
#  (Hamburg, Bucharest), (Bucharest, Hamburg),
#  (Helsinki, Hamburg), (Hamburg, Helsinki),
#  (Zurich, Hamburg), (Hamburg, Zurich),
#  (Zurich, Bucharest), (Bucharest, Zurich),
#  (Zurich, Split), (Split, Zurich),
#  (Helsinki, Split), (Split, Helsinki),
#  (Split, Hamburg), (Hamburg, Split).
allowed = [(1,2), (2,1),
           (0,3), (3,0),
           (2,0), (0,2),
           (1,0), (0,1),
           (1,3), (3,1),
           (1,4), (4,1),
           (2,4), (4,2),
           (4,0), (0,4)]

# For each consecutive segment pair, require there is a direct flight.
for i in range(4):
    pair = (seg[i], seg[i+1])
    s.add(Or([And(pair[0] == p, pair[1] == q) for (p, q) in allowed]))

# Special event constraints:
#  (1) Wedding in Zürich between day 1 and day 3.
# Since day 1 and day 2 are always in segment 0 and day 3 is in segment 0 if a1 >= 3 
# (or in segment 1 if a1 = 2), we require:
s.add(Implies(a1 >= 3, seg[0] == 1))    # If segment 0 lasts until (or past) day 3, then it must be Zürich.
s.add(Implies(a1 == 2, seg[1] == 1))     # Otherwise, if segment 0 is only 2 days, then day 3 (in seg 1) must be Zürich.

# (2) Conference in Split on day 4 and day 10.
# We model the fact that day d is “covered” by a segment i if d lies in its interval.
def in_interval(d):
    # Returns a list of conditions “d is in segment i”
    return [And(1 <= d, d <= a1),       # d in seg0: days 1..a1
            And(a1 <= d, d <= a2),      # d in seg1: days a1..a2
            And(a2 <= d, d <= a3),      # d in seg2: days a2..a3
            And(a3 <= d, d <= a4),      # d in seg3: days a3..a4
            And(a4 <= d, d <= 12)]      # d in seg4: days a4..12

for d in [4, 10]:
    # On day d at least one segment that covers it must be Split (city 4)
    conds = []
    conds.append(And(in_interval(d)[0], seg[0] == 4))
    conds.append(And(in_interval(d)[1], seg[1] == 4))
    conds.append(And(in_interval(d)[2], seg[2] == 4))
    conds.append(And(in_interval(d)[3], seg[3] == 4))
    conds.append(And(in_interval(d)[4], seg[4] == 4))
    s.add(Or(conds))

# Check for a solution.
if s.check() == sat:
    m = s.model()
    # Extract the flight days (boundaries)
    day_a1 = m[a1].as_long()
    day_a2 = m[a2].as_long()
    day_a3 = m[a3].as_long()
    day_a4 = m[a4].as_long()
    
    # Build the itinerary segments.
    # Segment 0 covers days 1 ... a1, etc.
    segments = [
        {"start_day": 1, "end_day": day_a1, "city": city_names[m[seg[0]].as_long()]},
        {"start_day": day_a1, "end_day": day_a2, "city": city_names[m[seg[1]].as_long()]},
        {"start_day": day_a2, "end_day": day_a3, "city": city_names[m[seg[2]].as_long()]},
        {"start_day": day_a3, "end_day": day_a4, "city": city_names[m[seg[3]].as_long()]},
        {"start_day": day_a4, "end_day": 12, "city": city_names[m[seg[4]].as_long()]}
    ]
    
    # Here is our final itinerary:
    output = {"itinerary": segments}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")