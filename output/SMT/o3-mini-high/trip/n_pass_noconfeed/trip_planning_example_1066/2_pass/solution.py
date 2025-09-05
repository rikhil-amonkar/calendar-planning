#!/usr/bin/env python3
import json
from z3 import *

# Mapping from city id to city name and required duration
city_names = {
    0: "Brussels",
    1: "Bucharest",
    2: "Stuttgart",
    3: "Mykonos",
    4: "Madrid",
    5: "Helsinki",
    6: "Split",
    7: "London"
}

durations = {
    0: 4,  # Brussels
    1: 3,  # Bucharest
    2: 4,  # Stuttgart
    3: 2,  # Mykonos
    4: 2,  # Madrid
    5: 5,  # Helsinki
    6: 3,  # Split
    7: 5   # London
}

# Allowed direct flights (bidirectional)
allowed_flights = [
    (0, 7), (7, 0),   # Brussels - London
    (0, 1), (1, 0),   # Brussels - Bucharest
    (0, 4), (4, 0),   # Brussels - Madrid
    (5, 7), (7, 5),   # Helsinki - London
    (5, 4), (4, 5),   # Helsinki - Madrid
    (5, 0), (0, 5),   # Helsinki - Brussels
    (6, 4), (4, 6),   # Split - Madrid
    (6, 5), (5, 6),   # Split - Helsinki
    (6, 7), (7, 6),   # Split - London
    (7, 3), (3, 7),   # London - Mykonos
    (7, 1), (1, 7),   # Bucharest - London
    (7, 2), (2, 7),   # Stuttgart - London
    (1, 4), (4, 1),   # Bucharest - Madrid
    (0, 4), (4, 0),   # Brussels - Madrid (already included above)
    (2, 6), (6, 2),   # Stuttgart - Split
    (3, 4), (4, 3)    # Mykonos - Madrid
]

# Function that returns a Z3 expression for the required duration based on city variable.
def get_duration_expr(city):
    return If(city == 0, durations[0],
           If(city == 1, durations[1],
           If(city == 2, durations[2],
           If(city == 3, durations[3],
           If(city == 4, durations[4],
           If(city == 5, durations[5],
           If(city == 6, durations[6],
           If(city == 7, durations[7],
              0))))))))  # Note the eight closing parentheses

# Create a Z3 solver instance
solver = Solver()

# We will plan an itinerary over 8 segments (one per city)
# order[i] is an Int variable representing the city ID visited in segment i.
order = [Int(f"order_{i}") for i in range(8)]
solver.add(Distinct(order))

# Constraint: Madrid (id 4) must be visited exactly once and must be the final city.
solver.add(order[7] == 4)
for i in range(7):
    solver.add(order[i] != 4)

# s[i] will denote the start day of segment i.
s = [Int(f"s_{i}") for i in range(8)]
for i in range(8):
    solver.add(s[i] >= 1, s[i] <= 21)

# The trip starts on Day 1.
solver.add(s[0] == 1)
# For Madrid (fixed at order[7]) because of the conference on Day 20-21,
# its start day must be exactly 20.
solver.add(s[7] == 20)

# Chain the segments.
# If you are in city A in a segment and fly to city B in the next, you take a direct flight on day s[i+1].
for i in range(7):
    dur_expr = get_duration_expr(order[i])
    solver.add(s[i+1] == s[i] + dur_expr - 1)

# Ensure that the final segment ends exactly on Day 21.
solver.add(s[7] + get_duration_expr(order[7]) - 1 == 21)

# Flight connection constraints:
# For every consecutive pair of cities, there must be a direct flight.
for i in range(7):
    possible_flights = []
    for (a, b) in allowed_flights:
        possible_flights.append(And(order[i] == a, order[i+1] == b))
    solver.add(Or(possible_flights))

# Friend meeting in Stuttgart:
# If Stuttgart (id 2) is visited, its start day must be at most Day 4.
for i in range(8):
    solver.add(Implies(order[i] == 2, s[i] <= 4))

# Solve the constraints and build the itinerary.
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(8):
        city_id = model.evaluate(order[i]).as_long()
        start_day = model.evaluate(s[i]).as_long()
        dur = durations[city_id]
        end_day = start_day + dur - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city_names[city_id]
        })
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print(json.dumps({"error": "No solution found"}))