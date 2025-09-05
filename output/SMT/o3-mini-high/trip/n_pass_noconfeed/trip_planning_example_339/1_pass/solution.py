from z3 import *
import json

# City codes and their properties
# 0: Warsaw (2 days), 1: Riga (7 days), 2: Budapest (7 days), 3: Paris (4 days)
cities = {0: "Warsaw", 1: "Riga", 2: "Budapest", 3: "Paris"}
durations = {0: 2, 1: 7, 2: 7, 3: 4}

# Create the solver
solver = Solver()

# We will have 4 segments. The first segment is fixed:
# Segment 0: city0 = Warsaw (0)
# Segments 1-3 are variables that must be a permutation of {Riga (1), Budapest (2), Paris (3)}
c1 = Int('c1')
c2 = Int('c2')
c3 = Int('c3')

# Domain constraints: c1, c2, c3 must be among 1, 2, 3
solver.add(Or(c1 == 1, c1 == 2, c1 == 3))
solver.add(Or(c2 == 1, c2 == 2, c2 == 3))
solver.add(Or(c3 == 1, c3 == 2, c3 == 3))
# They must be all different
solver.add(Distinct(c1, c2, c3))

# Define the day intervals for each segment.
# Each segment i has a start day s_i and an end day e_i. If a flight occurs on the transition day,
# that day counts in both segments.
s0, e0 = Int('s0'), Int('e0')
s1, e1 = Int('s1'), Int('e1')
s2, e2 = Int('s2'), Int('e2')
s3, e3 = Int('s3'), Int('e3')

# The trip starts on day 1.
solver.add(s0 == 1)
# For segment 0, city=Warsaw (code 0), so duration = durations[0]=2 days.
solver.add(e0 == s0 + durations[0] - 1)  # e0 = 1 + 2 - 1 = 2

# For segment 1: its start day equals e0 (flight day is counted in both segments)
solver.add(s1 == e0)
# Duration of segment 1 depends on the city: if c1==1 then 7 days, if c1==2 then 7 days, if c1==3 then 4 days.
solver.add(e1 == s1 + If(c1 == 1, durations[1], If(c1 == 2, durations[2], durations[3])) - 1)

# For segment 2:
solver.add(s2 == e1)
solver.add(e2 == s2 + If(c2 == 1, durations[1], If(c2 == 2, durations[2], durations[3])) - 1)

# For segment 3:
solver.add(s3 == e2)
solver.add(e3 == s3 + If(c3 == 1, durations[1], If(c3 == 2, durations[2], durations[3])) - 1)

# The trip finishes on day 17.
solver.add(e3 == 17)

# Define allowed direct flight transitions between two cities.
# Allowed flight pairs (bidirectional) are:
#   Warsaw (0) <-> Budapest (2)
#   Warsaw (0) <-> Riga (1)
#   Budapest (2) <-> Paris (3)
#   Warsaw (0) <-> Paris (3)
#   Paris (3) <-> Riga (1)
def allowed_transition(c_from, c_to):
    return Or(
        # From Warsaw: can fly to Riga, Budapest, or Paris.
        And(c_from == 0, Or(c_to == 1, c_to == 2, c_to == 3)),
        # From Riga: can fly to Warsaw or Paris.
        And(c_from == 1, Or(c_to == 0, c_to == 3)),
        # From Budapest: can fly to Warsaw or Paris.
        And(c_from == 2, Or(c_to == 0, c_to == 3)),
        # From Paris: can fly to Warsaw, Riga, or Budapest.
        And(c_from == 3, Or(c_to == 0, c_to == 1, c_to == 2))
    )

# Add flight constraints between consecutive segments.
# Segment 0 -> Segment 1: from Warsaw (0) to city in segment 1.
solver.add(allowed_transition(0, c1))
# Segment 1 -> Segment 2:
solver.add(allowed_transition(c1, c2))
# Segment 2 -> Segment 3:
solver.add(allowed_transition(c2, c3))

# Additional constraints:
# 1. Annual show in Warsaw is from day 1 to day 2.
#    We guarantee this as segment 0 is fixed to Warsaw with days 1-2.

# 2. Wedding in Riga takes place between day 11 and day 17.
#    If a segment is in Riga (code 1), then its interval must cover at least one day
#    within [11, 17]. Since the trip ends on day 17, it suffices to force the segment's end to be >= 11.
solver.add(Implies(0 == 1, e0 >= 11))  # This is a no-op for segment 0 (Warsaw).
solver.add(Implies(c1 == 1, e1 >= 11))
solver.add(Implies(c2 == 1, e2 >= 11))
solver.add(Implies(c3 == 1, e3 >= 11))

# Compute a solution using Z3
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    # Segment 0 is fixed to Warsaw.
    itinerary.append({
        "day_range": f"Day {model[s0]}-{model[e0]}",
        "place": cities[0]
    })
    # Segment 1:
    seg1_city = model[c1].as_long()
    itinerary.append({
        "day_range": f"Day {model[s1]}-{model[e1]}",
        "place": cities[seg1_city]
    })
    # Segment 2:
    seg2_city = model[c2].as_long()
    itinerary.append({
        "day_range": f"Day {model[s2]}-{model[e2]}",
        "place": cities[seg2_city]
    })
    # Segment 3:
    seg3_city = model[c3].as_long()
    itinerary.append({
        "day_range": f"Day {model[s3]}-{model[e3]}",
        "place": cities[seg3_city]
    })
    output = {"itinerary": itinerary}
    print(json.dumps(output))
else:
    print(json.dumps({"itinerary": []}))