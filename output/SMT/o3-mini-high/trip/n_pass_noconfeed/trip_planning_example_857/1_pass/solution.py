from z3 import *
import json

# Define city indices and their corresponding durations.
# Mapping: 0: Porto, 1: Geneva, 2: Mykonos, 3: Manchester, 4: Hamburg, 5: Naples, 6: Frankfurt
city_names = ["Porto", "Geneva", "Mykonos", "Manchester", "Hamburg", "Naples", "Frankfurt"]
durations = {0: 2, 1: 3, 2: 3, 3: 4, 4: 5, 5: 5, 6: 2}

# Allowed direct flight connections (bidirectional)
allowed_edges = [
    (4, 6), (6, 4),
    (5, 2), (2, 5),
    (4, 0), (0, 4),
    (4, 1), (1, 4),  # from Hamburg to Geneva (assumed symmetric)
    (2, 1), (1, 2),
    (6, 1), (1, 6),
    (6, 0), (0, 6),
    (1, 0), (0, 1),
    (1, 3), (3, 1),
    (5, 3), (3, 5),
    (6, 5), (5, 6),
    (6, 3), (3, 6),
    (5, 1), (1, 5),
    (0, 3), (3, 0),
    (4, 3), (3, 4)
]

# There are 7 segments (visiting 7 cities)
num_segments = 7

# Create Z3 solver instance
solver = Solver()

# Create variables for the route ordering, start days (S) and end days (E) for each segment.
route = [Int(f"route_{i}") for i in range(num_segments)]
S = [Int(f"S_{i}") for i in range(num_segments)]
E = [Int(f"E_{i}") for i in range(num_segments)]

# Each route variable must be between 0 and 6 (each representing a city)
for i in range(num_segments):
    solver.add(And(route[i] >= 0, route[i] <= 6))

# All cities must be visited exactly once
solver.add(Distinct(route))

# For each segment, enforce the duration condition:
# E[i] - S[i] + 1 equals the fixed days for the city chosen at route[i]
for i in range(num_segments):
    solver.add(
        If(route[i] == 0, E[i] - S[i] + 1 == durations[0],
        If(route[i] == 1, E[i] - S[i] + 1 == durations[1],
        If(route[i] == 2, E[i] - S[i] + 1 == durations[2],
        If(route[i] == 3, E[i] - S[i] + 1 == durations[3],
        If(route[i] == 4, E[i] - S[i] + 1 == durations[4],
        If(route[i] == 5, E[i] - S[i] + 1 == durations[5],
        E[i] - S[i] + 1 == durations[6]))))))
    )

# The itinerary starts on day 1.
solver.add(S[0] == 1)

# For consecutive segments, the flight day is the overlapping day: 
# The next segment starts on the day the previous segment ends.
for i in range(num_segments - 1):
    solver.add(S[i+1] == E[i])

# The end day of the final segment determines the total itinerary days.
solver.add(E[num_segments - 1] == 18)

# Add event-specific constraints for the cities:
for i in range(num_segments):
    # If Frankfurt is visited, must cover the annual show from day 5 to 6.
    solver.add(Implies(route[i] == 6, And(S[i] <= 5, E[i] >= 6)))
    
    # If Mykonos is visited, must meet friend between day 10 and day 12.
    solver.add(Implies(
        route[i] == 2,
        Or(And(S[i] <= 10, E[i] >= 10),
           And(S[i] <= 11, E[i] >= 11),
           And(S[i] <= 12, E[i] >= 12))
    ))
    
    # If Manchester is visited, wedding must be attended between day 15 and day 18.
    solver.add(Implies(
        route[i] == 3,
        Or(And(S[i] <= 15, E[i] >= 15),
           And(S[i] <= 16, E[i] >= 16),
           And(S[i] <= 17, E[i] >= 17),
           And(S[i] <= 18, E[i] >= 18))
    ))

# Add direct flight connectivity constraints for consecutive segments.
for i in range(num_segments - 1):
    # For segments i and i+1, the flight connection must be one of the allowed pairs.
    conn_constraints = [And(route[i] == a, route[i+1] == b) for (a, b) in allowed_edges]
    solver.add(Or(conn_constraints))

# Optional: Ensure start and end days lie within itinerary's limits.
for i in range(num_segments):
    solver.add(S[i] >= 1)
    solver.add(E[i] >= S[i])
    solver.add(E[i] <= 18)

# Check solver and extract solution if one exists.
if solver.check() == sat:
    m = solver.model()
    itinerary = []
    for i in range(num_segments):
        start_day = m.evaluate(S[i]).as_long()
        end_day = m.evaluate(E[i]).as_long()
        city_index = m.evaluate(route[i]).as_long()
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city_names[city_index]
        })
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))