from z3 import *
import json

# Map cities to integers:
# 0: Valencia, 1: Athens, 2: Naples, 3: Zurich
# Durations: Valencia=6, Athens=6, Zurich=6, Naples=5
def duration(city):
    return If(city == 2, 5, 6)

# Allowed flight connection.
def flight_allowed(a, b):
    return Or(
        And(a == 0, b == 2),
        And(a == 2, b == 0),
        And(a == 0, b == 1),  # Valencia -> Athens (only this direction)
        And(a == 1, b == 2),
        And(a == 2, b == 1),
        And(a == 3, b == 2),
        And(a == 2, b == 3),
        And(a == 1, b == 3),
        And(a == 3, b == 1),
        And(a == 3, b == 0),
        And(a == 0, b == 3)
    )

# Create the solver
s = Solver()

# Define segment city choice variables for 4 segments.
x1 = Int('x1')
x2 = Int('x2')
x3 = Int('x3')
x4 = Int('x4')

# Their domain is 0..3 and they must be distinct.
s.add(And(x1 >= 0, x1 <= 3))
s.add(And(x2 >= 0, x2 <= 3))
s.add(And(x3 >= 0, x3 <= 3))
s.add(And(x4 >= 0, x4 <= 3))
s.add(Distinct(x1, x2, x3, x4))

# In addition, because Naples (city 2) must host the wedding between Day 16 and Day 20,
# and the flight-day overlap forces Naples to be later in the trip,
# we force Naples to be the final city.
s.add(x4 == 2)

# Define start day variables for each segment.
S1 = Int('S1')
S2 = Int('S2')
S3 = Int('S3')
S4 = Int('S4')

# Set timeline: if a flight occurs on day X, you are in both the origin and destination on that day.
# Let segment i start on S_i. Then if the duration in that city is d, segment covers days S_i to S_i + d - 1.
# And the next segment starts on the same day as the previous segment's end.
s.add(S1 == 1)
s.add(S2 == S1 + duration(x1) - 1)
s.add(S3 == S2 + duration(x2) - 1)
s.add(S4 == S3 + duration(x3) - 1)
# The final segment (x4, which is Naples) must end on Day 20.
s.add(S4 + duration(x4) - 1 == 20)

# Apply flight connectivity constraints for consecutive segments.
s.add(flight_allowed(x1, x2))
s.add(flight_allowed(x2, x3))
s.add(flight_allowed(x3, x4))

# Constraint: You want to visit relatives in Athens (city 1) between day 1 and day 6.
# This is forced by requiring that if a segment is in Athens then its start day is at most 6.
s.add(Implies(x1 == 1, S1 <= 6))
s.add(Implies(x2 == 1, S2 <= 6))
s.add(Implies(x3 == 1, S3 <= 6))
s.add(Implies(x4 == 1, S4 <= 6))

# Constraint: You want to attend a wedding in Naples (city 2) between day 16 and day 20.
# This requires that if a segment is Naples then its interval [S, S + duration - 1] intersects [16, 20].
# For Naples duration = 5, a sufficient condition is S + 5 - 1 >= 16, i.e. S >= 12.
s.add(Implies(x1 == 2, S1 >= 12))
s.add(Implies(x2 == 2, S2 >= 12))
s.add(Implies(x3 == 2, S3 >= 12))
s.add(Implies(x4 == 2, S4 >= 12))

# Note: The required durations in each city are built into the duration function:
# Valencia, Athens, and Zurich get 6 days each; Naples gets 5 days.
# Since the overall sum of durations minus overlaps must equal 20,
# we have: (6 + 6 + 6 + 5) - 3 = 20.

# Solve for a valid itinerary.
if s.check() == sat:
    m = s.model()
    order = [m[x1].as_long(), m[x2].as_long(), m[x3].as_long(), m[x4].as_long()]
    # Map integers to city names.
    cities = {0: "Valencia", 1: "Athens", 2: "Naples", 3: "Zurich"}
    
    # Compute start and end days for each segment based on the model.
    S1_val = m[S1].as_long()
    d1 = 5 if order[0] == 2 else 6
    E1_val = S1_val + d1 - 1

    S2_val = m[S2].as_long()
    d2 = 5 if order[1] == 2 else 6
    E2_val = S2_val + d2 - 1

    S3_val = m[S3].as_long()
    d3 = 5 if order[2] == 2 else 6
    E3_val = S3_val + d3 - 1

    S4_val = m[S4].as_long()
    d4 = 5 if order[3] == 2 else 6
    E4_val = S4_val + d4 - 1

    itinerary = [
        {"day_range": f"Day {S1_val}-{E1_val}", "place": cities[order[0]]},
        {"day_range": f"Day {S2_val}-{E2_val}", "place": cities[order[1]]},
        {"day_range": f"Day {S3_val}-{E3_val}", "place": cities[order[2]]},
        {"day_range": f"Day {S4_val}-{E4_val}", "place": cities[order[3]]}
    ]
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))