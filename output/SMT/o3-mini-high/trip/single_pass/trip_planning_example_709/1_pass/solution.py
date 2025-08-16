from z3 import *
import json

# Define the six cities and their required days.
cities = ["Dubrovnik", "Helsinki", "Reykjavik", "Prague", "Valencia", "Porto"]
# Their durations (in days) – note the total is 4+4+4+3+5+3 = 23.
durations = [4, 4, 4, 3, 5, 3]

# Allowed direct flight connections (bidirectional). Our mapping of cities is:
# 0: Dubrovnik, 1: Helsinki, 2: Reykjavik, 3: Prague, 4: Valencia, 5: Porto.
# The given allowed flights are:
# - Helsinki and Prague         → (1,3) and (3,1)
# - Prague and Valencia         → (3,4) and (4,3)
# - Valencia and Porto          → (4,5) and (5,4)
# - Helsinki and Reykjavik      → (1,2) and (2,1)
# - Dubrovnik and Helsinki      → (0,1) and (1,0)
# - Reykjavik and Prague        → (2,3) and (3,2)
allowed_edges = {
    (0, 1), (1, 0),
    (1, 3), (3, 1),
    (3, 4), (4, 3),
    (4, 5), (5, 4),
    (1, 2), (2, 1),
    (2, 3), (3, 2)
}

solver = Solver()

# We have 6 segments. Create a list for the “order” of city visits.
# order[i] is an Int in 0..5 representing which city is visited as the i-th segment.
order = [Int(f"order_{i}") for i in range(6)]
for o in order:
    solver.add(o >= 0, o <= 5)
solver.add(Distinct(order))

# Create a list of start days for each segment.
# Remember, if a segment starts on day S and its duration is d, then that visit covers days S .. S+d-1.
s = [Int(f"s_{i}") for i in range(6)]
# The first visit must start on day 1.
solver.add(s[0] == 1)

# Helper function: given a city index (unknown in the model) return its duration.
def duration_expr(city_expr):
    return If(city_expr == 0, durations[0],
           If(city_expr == 1, durations[1],
           If(city_expr == 2, durations[2],
           If(city_expr == 3, durations[3],
           If(city_expr == 4, durations[4],
              durations[5])))))

# For segments 0 to 4, if city in segment i has duration d then the next segment starts on s[i] + d - 1.
for i in range(5):
    solver.add(s[i+1] == s[i] + duration_expr(order[i]) - 1)

# The total calendar days must equal 18.
# That is, for the last segment: s[5] + (its duration) - 1 == 18.
solver.add(s[5] + duration_expr(order[5]) - 1 == 18)

# Enforce that each flight (i.e. transition from segment i to i+1) is allowed.
for i in range(5):
    valid_transitions = []
    for (a, b) in allowed_edges:
        valid_transitions.append(And(order[i] == a, order[i+1] == b))
    solver.add(Or(valid_transitions))

# Add the meeting friend constraint:
# If you visit Porto (city index 5) then some day in that segment must be between day 16 and day 18.
# In other words, if segment i is Porto then its start day s[i] must be such that
# s[i] <= 18 and s[i] + 3 - 1 >= 16 (since Porto’s duration is 3).
for i in range(6):
    solver.add(Implies(order[i] == 5, And(s[i] <= 18, s[i] + durations[5] - 1 >= 16)))

# Solve the constraints.
if solver.check() == sat:
    model = solver.model()
    sol_order = [model.evaluate(order[i]).as_long() for i in range(6)]
    sol_s = [model.evaluate(s[i]).as_long() for i in range(6)]
    
    # Build the itinerary segments.
    itinerary_segments = []
    for i in range(6):
        city = cities[sol_order[i]]
        start_day = sol_s[i]
        d = durations[sol_order[i]]
        end_day = start_day + d - 1
        # Each segment is described by the day range (note that the flight day is shared)
        itinerary_segments.append({"city": city, "days": f"{start_day}-{end_day}"})
    
    # Print the itinerary as a JSON-formatted dictionary.
    print(json.dumps({"itinerary": itinerary_segments}, indent=2))
else:
    print("No solution found")