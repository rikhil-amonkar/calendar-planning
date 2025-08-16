from z3 import *
import json

# Define cities and their indices
cities = ['Paris', 'Florence', 'Vienna', 'Porto', 'Munich', 'Nice', 'Warsaw']
city_index = {city: idx for idx, city in enumerate(cities)}

# Define allowed transitions
allowed_transitions = set()

# Helper to add bidirectional transitions
def add_transition(a, b):
    allowed_transitions.add((a, b))
    allowed_transitions.add((b, a))

# List of direct flights (bidirectional)
add_transition(1, 2)  # Florence and Vienna
add_transition(0, 6)  # Paris and Warsaw
add_transition(4, 2)  # Munich and Vienna
add_transition(3, 2)  # Porto and Vienna
add_transition(6, 2)  # Warsaw and Vienna
add_transition(1, 4)  # Florence to Munich
add_transition(4, 6)  # Munich and Warsaw
add_transition(4, 5)  # Munich and Nice
add_transition(0, 1)  # Paris and Florence
add_transition(6, 5)  # Warsaw and Nice
add_transition(3, 4)  # Porto and Munich
add_transition(3, 5)  # Porto and Nice
add_transition(0, 2)  # Paris and Vienna
add_transition(5, 2)  # Nice and Vienna
add_transition(3, 0)  # Porto and Paris
add_transition(0, 5)  # Paris and Nice
add_transition(0, 4)  # Paris and Munich
add_transition(3, 6)  # Porto and Warsaw

# Create Z3 solver
solver = Solver()

# Create variables for each day (1-20)
days = 20
city_vars = [Int(f'city_{d}') for d in range(days)]

# Add constraints that city variables are within 0-6
for d in range(days):
    solver.add(And(city_vars[d] >= 0, city_vars[d] <= 6))

# Event constraints: at least one day in each event city during specified period
# Porto between day 1-3 (indices 0,1,2)
solver.add(Or(city_vars[0] == 3, city_vars[1] == 3, city_vars[2] == 3))
# Warsaw between day 13-15 (indices 12,13,14)
solver.add(Or(city_vars[12] == 6, city_vars[13] == 6, city_vars[14] == 6))
# Vienna between day 19-20 (indices 18,19)
solver.add(Or(city_vars[18] == 2, city_vars[19] == 2))

# Add transition constraints between consecutive days
for d in range(days - 1):
    from_city = city_vars[d]
    to_city = city_vars[d + 1]
    constraints = []
    for a, b in allowed_transitions:
        constraints.append(And(from_city == a, to_city == b))
    solver.add(Or(*constraints))

# Required durations for each city
required_days = [5, 3, 2, 3, 5, 5, 3]  # Paris, Florence, Vienna, Porto, Munich, Nice, Warsaw

# Add duration constraints
for c in range(7):
    count_in = Sum([If(city_vars[d] == c, 1, 0) for d in range(days)])
    count_departure = Sum([If(And(city_vars[d] == c, city_vars[d] != city_vars[d + 1]), 1, 0) for d in range(days - 1)])
    total_days = count_in + count_departure
    solver.add(total_days == required_days[c])

# Check for solution
if solver.check() == sat:
    model = solver.model()
    # Extract the itinerary
    itinerary = []
    for d in range(days):
        city_idx = model[city_vars[d]].as_long()
        itinerary.append({f"Day {d+1}": cities[city_idx]})
    # Output JSON
    print(json.dumps({'itinerary': itinerary}, indent=2))
else:
    print("No solution found.")