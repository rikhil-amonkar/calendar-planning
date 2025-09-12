import z3
import json

# Initialize Z3 solver
solver = z3.Solver()

# Define city variables (0: Mykonos, 1: Budapest, 2: Hamburg)
c1, c2, c3 = [z3.Int(f'c{i}') for i in range(1, 4)]
d1, d2, d3 = [z3.Int(f'd{i}') for i in range(1, 4)]

# All cities are distinct
solver.add(z3.Distinct(c1, c2, c3))

# Transition constraints between c1 and c2
allowed_transitions_c1c2 = [
    z3.And(c1 == 0, c2 == 1),
    z3.And(c1 == 1, c2 == 0),
    z3.And(c1 == 1, c2 == 2),
    z3.And(c1 == 2, c2 == 1),
]
solver.add(z3.Or(*allowed_transitions_c1c2))

# Transition constraints between c2 and c3
allowed_transitions_c2c3 = [
    z3.And(c2 == 0, c3 == 1),
    z3.And(c2 == 1, c3 == 0),
    z3.And(c2 == 1, c3 == 2),
    z3.And(c2 == 2, c3 == 1),
]
solver.add(z3.Or(*allowed_transitions_c2c3))

# Duration constraints based on city
for city_var, dur_var in [(c1, d1), (c2, d2), (c3, d3)]:
    solver.add(z3.Implies(city_var == 0, dur_var >= 6))
    solver.add(z3.Implies(city_var == 1, dur_var >= 3))
    solver.add(z3.Implies(city_var == 2, dur_var >= 2))

# Sum of durations is 11
solver.add(d1 + d2 + d3 == 11)

# If Mykonos is third city, then d1 + d2 <= 5
solver.add(z3.Implies(c3 == 0, d1 + d2 <= 5))

if solver.check() == z3.sat:
    model = solver.model()
    # Extract city order and durations
    cities_order = [model[c].as_long() for c in [c1, c2, c3]]
    durations = [model[d].as_long() for d in [d1, d2, d3]]
    city_names = {0: 'Mykonos', 1: 'Budapest', 2: 'Hamburg'}
    # Compute day ranges
    itinerary = []
    start_day = 1
    for i in range(3):
        end_day = start_day + durations[i] - 1
        city_name = city_names[cities_order[i]]
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city_name})
        start_day = end_day
    # Generate JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"error": "No solution found"}))