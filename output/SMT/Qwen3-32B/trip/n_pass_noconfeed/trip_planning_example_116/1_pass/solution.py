import json
from z3 import *

solver = Solver()

# Define variables for the cities in each segment (0: Split, 1: London, 2: Santorini)
C1, C2, C3 = Ints('C1 C2 C3')

# Define variables for the end days of each segment
e1, e2 = Ints('e1 e2')

# Cities must be in the set {0, 1, 2}
solver.add(Or(C1 == 0, C1 == 1, C1 == 2))
solver.add(Or(C2 == 0, C2 == 1, C2 == 2))
solver.add(Or(C3 == 0, C3 == 1, C3 == 2))

# Allowed transitions between C1 and C2
solver.add(Or(
    And(C1 == 0, C2 == 1),  # Split → London
    And(C1 == 1, C2 == 0),  # London → Split
    And(C1 == 1, C2 == 2),  # London → Santorini
    And(C1 == 2, C2 == 1)   # Santorini → London
))

# Allowed transitions between C2 and C3
solver.add(Or(
    And(C2 == 0, C3 == 1),  # Split → London
    And(C2 == 1, C3 == 0),  # London → Split
    And(C2 == 1, C3 == 2),  # London → Santorini
    And(C2 == 2, C3 == 1)   # Santorini → London
))

# Conference days must be in Santorini (C3 == 2)
solver.add(C3 == 2)

# Santorini's duration constraint: 18 - e2 +1 ==7 → e2=12
solver.add(18 - e2 + 1 == 7)

# Conference day 12 must be in Santorini's segment (third segment)
# Third segment starts on e2 and ends on 18 → e2 <=12
solver.add(e2 <= 12)

# Therefore, e2 must be 12
# Now, since C3 is Santorini (2), and transition between C2 and C3 must be allowed, C2 must be 1 (London)
solver.add(C2 == 1)

# Now, transition between C1 and C2 (which is 1) must be allowed. Since C2 is 1 (London), C1 can be 0 (Split) or 2 (Santorini)
# But if C1 is 2, then Split's duration is e1 days, which must be 6. Let's see if that's possible.
# However, if C1 is 2 (Santorini), then the first segment is Santorini from day 1 to e1. But required Santorini duration is 7 days. So e1=7. Then London's duration is e2 - e1 +1 =12 -7 +1=6, which is less than required 7. Hence, invalid. So C1 must be 0 (Split)
solver.add(C1 == 0)

# Split's duration is e1 days → e1 ==6
solver.add(e1 == 6)

# London's duration is e2 - e1 +1 ==7
solver.add(e2 - e1 +1 == 7)

if solver.check() == sat:
    model = solver.model()
    e1_val = model[e1].as_long()
    e2_val = model[e2].as_long()
    # Generate the itinerary
    itinerary = [
        {"day_range": f"Day 1-{e1_val}", "place": "Split"},
        {"day_range": f"Day {e1_val}-{e2_val}", "place": "London"},
        {"day_range": f"Day {e2_val}-18", "place": "Santorini"}
    ]
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found")