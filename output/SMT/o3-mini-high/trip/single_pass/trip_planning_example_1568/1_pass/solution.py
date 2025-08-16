from z3 import *
import json

# There are 10 cities with indices:
# 0: Prague
# 1: Brussels
# 2: Riga
# 3: Munich
# 4: Seville
# 5: Stockholm
# 6: Istanbul
# 7: Amsterdam
# 8: Vienna
# 9: Split

# Required days (stay durations) for each city.
# Note: On a flight day, you “count” that day for both the city you are leaving and the one you are arriving.
req = [5, 2, 2, 2, 3, 2, 2, 3, 5, 3]
# Define D = req - 1, representing the “extra” days beyond the start day.
D = [r - 1 for r in req]

# Allowed flight connections (both directions).
# Each tuple (a,b) indicates that a direct flight exists between city a and city b.
allowed_pairs = [
  (2,5), (5,2),
  (5,1), (1,5),
  (6,3), (3,6),
  (6,2), (2,6),
  (0,9), (9,0),
  (8,1), (1,8),
  (8,2), (2,8),
  (9,5), (5,9),
  (3,7), (7,3),
  (9,7), (7,9),
  (7,5), (5,7),
  (7,2), (2,7),
  (8,5), (5,8),
  (8,6), (6,8),
  (8,4), (4,8),
  (6,7), (7,6),
  (3,1), (1,3),
  (0,3), (3,0),
  (2,3), (3,2),
  (0,7), (7,0),
  (0,1), (1,0),
  (0,6), (6,0),
  (6,5), (5,6),
  (8,0), (0,8),
  (3,9), (9,3),
  (8,7), (7,8),
  (0,5), (5,0),
  (1,4), (4,1),
  (3,5), (5,3),
  (6,1), (1,6),
  (7,4), (4,7),
  (8,9), (9,8),
  (3,4), (4,3),
  (2,1), (1,2),
  (0,2), (2,0),
  (8,3), (3,8)
]

# Create a Z3 Solver
s = Solver()

num_segments = 10  # one segment per city visited

# Create an array "order" of length 10.
# order[i] is an Int representing the city visited in segment i.
order = [Int(f"order_{i}") for i in range(num_segments)]
for i in range(num_segments):
    s.add(order[i] >= 0, order[i] < 10)
s.add(Distinct(order))  # each city is visited exactly once

# Define start-day variables S[i] for each segment i.
S_vars = [Int(f"S_{i}") for i in range(num_segments)]
# For convenience, we also define an expression for the end-day E[i] = S[i] + req - 1.
def E_expr(i):
    # E[i] depends on which city is assigned to segment i.
    # That is: E[i] = S_vars[i] + (req[ order[i] ] - 1)
    return S_vars[i] + Sum([If(order[i] == j, req[j] - 1, 0) for j in range(10)])

# Constrain the first segment to start on Day 1.
s.add(S_vars[0] == 1)

# The segments are linked: for i > 0, S[i] = E[i-1]
for i in range(1, num_segments):
    s.add(S_vars[i] == E_expr(i-1))

# The overall trip must end on Day 20 (i.e. end day of the last segment is 20).
s.add(E_expr(num_segments - 1) == 20)
# (Note: the sum of (req-1) for all cities is 19 so 1 + 19 = 20, as required.)

# Special day constraints for certain cities:
for i in range(num_segments):
    # If visiting Prague then you must attend the annual show from Day 5 to 9.
    # Prague has req=5 so its interval is 5 days. To include days 5-9, the segment must start on Day 5.
    s.add(Implies(order[i] == 0, S_vars[i] == 5))
    
    # For Stockholm the conference occurs on Days 16 and 17.
    # Stockholm (req=2) must therefore start on Day 16 (interval: 16-17).
    s.add(Implies(order[i] == 5, S_vars[i] == 16))
    
    # Vienna: meet a friend between Days 1 and 5.
    # Vienna (req=5) stays 5 days; ensuring at least one day is in [1,5] forces its start to be <= 5.
    s.add(Implies(order[i] == 8, S_vars[i] <= 5))
    
    # Riga: meet friends between Days 15 and 16; Riga (req=2) has a 2-day interval.
    # To cover at least one of {15, 16} the start day must be between 14 and 16.
    s.add(Implies(order[i] == 2, And(S_vars[i] >= 14, S_vars[i] <= 16)))
    
    # Split: visit relatives between Days 11 and 13; Split (req=3) interval is [S, S+2].
    # We require the interval to intersect [11,13], which is ensured by S in [9, 13].
    s.add(Implies(order[i] == 9, And(S_vars[i] >= 9, S_vars[i] <= 13)))

# Flight connectivity: if you fly (direct) from city A in segment i to city B in segment i+1,
# then (A,B) must be in the allowed flight connections.
for i in range(num_segments - 1):
    conds = []
    for (a, b) in allowed_pairs:
        conds.append(And(order[i] == a, order[i+1] == b))
    s.add(Or(conds))

# Solve the constraints
if s.check() == sat:
    m = s.model()
    
    # Recover the order and start times from the model.
    seg_order = [m.evaluate(order[i]).as_long() for i in range(num_segments)]
    seg_start = [m.evaluate(S_vars[i]).as_long() for i in range(num_segments)]
    seg_end = [m.evaluate(E_expr(i)).as_long() for i in range(num_segments)]
    
    # City names
    cities = ["Prague", "Brussels", "Riga", "Munich", "Seville",
              "Stockholm", "Istanbul", "Amsterdam", "Vienna", "Split"]
    
    # Build segments info (for debugging, one may print these)
    segments = []
    for i in range(num_segments):
        city = cities[seg_order[i]]
        start = seg_start[i]
        end = seg_end[i]
        segments.append((city, start, end))
    # Uncomment next line to see segments summary:
    # print("Segments (city, start, end):", segments)
    
    # Build the itinerary day by day.
    # On a flight day (S_vars[i] = E_expr(i-1) for i>=1), that day belongs to both segments.
    itinerary = []
    # For each day from 1 to 20, check which segments cover that day.
    for d in range(1, 21):
        cities_today = []
        for i in range(num_segments):
            start = seg_start[i]
            end = seg_end[i]
            if start <= d <= end:
                cities_today.append(cities[seg_order[i]])
        itinerary.append({"day": d, "cities": cities_today})
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")