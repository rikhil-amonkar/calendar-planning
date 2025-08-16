from z3 import *
import json

# We'll index the cities as follows:
# 0: Helsinki (2 days)        [Workshop must occur on day 1 or 2 → start <= 2]
# 1: Warsaw   (3 days)         [Relatives visit requires an overlap with days 9-11 → start in [7,11]]
# 2: Madrid   (4 days)
# 3: Split    (4 days)
# 4: Reykjavik (2 days)        [Friend meeting requires an overlap with days 8-9 → start in [7,9]]
# 5: Budapest (4 days)

city_names = {0: "Helsinki", 1: "Warsaw", 2: "Madrid", 3: "Split", 4: "Reykjavik", 5: "Budapest"}
durations = {0: 2, 1: 3, 2: 4, 3: 4, 4: 2, 5: 4}

# Allowed direct flights (each as a pair (a,b) meaning you can fly from a to b on the flight day)
allowed_pairs = [
    (0, 4), (4, 0),        # Helsinki <--> Reykjavik
    (5, 1), (1, 5),        # Budapest <--> Warsaw
    (2, 3), (3, 2),        # Madrid <--> Split
    (0, 3), (3, 0),        # Helsinki <--> Split
    (0, 2), (2, 0),        # Helsinki <--> Madrid
    (0, 5), (5, 0),        # Helsinki <--> Budapest
    (4, 1), (1, 4),        # Reykjavik <--> Warsaw
    (0, 1), (1, 0),        # Helsinki <--> Warsaw
    (2, 5), (5, 2),        # Madrid <--> Budapest
    (5, 4), (4, 5),        # Budapest <--> Reykjavik
    (2, 1), (1, 2),        # Madrid <--> Warsaw
    (1, 3), (3, 1),        # Warsaw <--> Split
    (4, 2)                 # only allowed from Reykjavik to Madrid
]

# Create a Z3 solver
solver = Solver()

# There are 6 visits in order (positions 0..5).
num = 6

# order[i] will be an Int in {0,...,5} representing which city is visited in the i-th segment.
order = [Int(f'order_{i}') for i in range(num)]
for o in order:
    solver.add(And(o >= 0, o <= 5))
solver.add(Distinct(order))

# S[i] is the start day for the city visited in order[i].
S = [Int(f'S_{i}') for i in range(num)]
solver.add(S[0] == 1)  # trip always starts on day 1

# A helper: given a Z3 expression "c" for the city index, return its duration.
def get_duration(c):
    return If(c == 0, durations[0],
           If(c == 1, durations[1],
           If(c == 2, durations[2],
           If(c == 3, durations[3],
           If(c == 4, durations[4],
           If(c == 5, durations[5], 0))))))

# The visits are “chained” with overlap on the flight day:
# If you fly from city A (in position i) to city B (position i+1), then S[i+1] must equal S[i] + duration(A) - 1.
for i in range(num - 1):
    solver.add( S[i+1] == S[i] + get_duration(order[i]) - 1 )

# The end of the last city must be day 14.
# (Since the block for city i runs from S[i] to S[i] + duration - 1, for the last city:
solver.add( S[num-1] + get_duration(order[num-1]) - 1 == 14 )

# Add the flight-connection constraints: for each consecutive pair,
# the pair (order[i], order[i+1]) must be in the allowed pairs.
for i in range(num - 1):
    a = order[i]
    b = order[i+1]
    flight_ok = Or([And(a == ap, b == bp) for (ap, bp) in allowed_pairs])
    solver.add(flight_ok)

# City-specific scheduling constraints:
for i in range(num):
    # If this segment is Helsinki then its block must include day 1 or day 2 (i.e. start day <= 2)
    solver.add(Implies(order[i] == 0, S[i] <= 2))
    # If this segment is Warsaw then its block [S, S+2] must hit days 9..11. (S in [7, 11]).
    solver.add(Implies(order[i] == 1, And(S[i] >= 7, S[i] <= 11)))
    # If this segment is Reykjavik (2 days) then its block [S, S+1] must hit days 8..9 (so S in [7, 9]).
    solver.add(Implies(order[i] == 4, And(S[i] >= 7, S[i] <= 9)))
    
# (The other cities have no extra time‐window constraints.)

# Check for a solution
if solver.check() == sat:
    model = solver.model()
    itinerary_segments = []
    for i in range(num):
        # Evaluate which city is at position i and its start day.
        city_val = model.evaluate(order[i]).as_long()
        start_day = model.evaluate(S[i]).as_long()
        d = durations[city_val]
        end_day = start_day + d - 1
        itinerary_segments.append({
            "city": city_names[city_val],
            "start_day": start_day,
            "end_day": end_day
        })
    result = {"itinerary": itinerary_segments}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")