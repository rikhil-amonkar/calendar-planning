from z3 import *
import json

# Define city codes
CITIES = ['Vienna', 'Milan', 'Rome', 'Riga', 'Lisbon', 'Vilnius', 'Oslo']
duration = {0: 4, 1: 2, 2: 3, 3: 2, 4: 3, 5: 4, 6: 3}

allowed_pairs = [
    (3, 6), (6, 3),  # Riga-Oslo
    (2, 6), (6, 2),  # Rome-Oslo
    (0, 1), (1, 0),  # Vienna-Milan
    (0, 5), (5, 0),  # Vienna-Vilnius
    (0, 4), (4, 0),  # Vienna-Lisbon
    (3, 1), (1, 3),  # Riga-Milan
    (4, 6), (6, 4),  # Lisbon-Oslo
    (2, 3), (3, 2),  # Rome-Riga
    (2, 4), (4, 2),  # Rome-Lisbon
    (0, 3), (3, 0),  # Vienna-Riga
    (0, 2), (2, 0),  # Vienna-Rome
    (1, 6), (6, 1),  # Milan-Oslo
    (0, 6), (6, 0),  # Vienna-Oslo
    (5, 6), (6, 5),  # Vilnius-Oslo
    (3, 5), (5, 3),  # Riga-Vilnius
    (5, 1), (1, 5),  # Vilnius-Milan
    (3, 4), (4, 3),  # Riga-Lisbon
    (1, 4), (4, 1),  # Milan-Lisbon
]

# Create Z3 solver
solver = Solver()

# Create variables for the sequence (7 cities)
seq = [Int(f'seq_{i}') for i in range(7)]

# Constraints for the sequence
# 1. All distinct
solver.add(Distinct(seq))
# 2. First city is Vienna (0)
solver.add(seq[0] == 0)

# Create variables for start days
S = [Int(f'S_{i}') for i in range(7)]

# Constraints for start days
solver.add(S[0] == 1)
for i in range(1, 7):
    solver.add(S[i] == S[i-1] + duration[seq[i-1]] - 1)

# Constraints for Lisbon (4) and Oslo (6) start days
for i in range(7):
    # For Lisbon
    solver.add(If(seq[i] == 4, S[i] == 11, True == True))
    # For Oslo
    solver.add(If(seq[i] == 6, S[i] == 13, True == True))

# Constraints for transitions between consecutive cities
for i in range(6):
    # Check if (seq[i], seq[i+1]) is in allowed_pairs
    allowed_expr = Or([And(seq[i] == a, seq[i+1] == b) for a, b in allowed_pairs])
    solver.add(allowed_expr)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    # Extract the sequence
    sequence = [model.evaluate(seq[i]).as_long() for i in range(7)]
    # Extract start days
    start_days = [model.evaluate(S[i]).as_long() for i in range(7)]
    # Now build the itinerary
    itinerary = []
    for i in range(7):
        city_code = sequence[i]
        city_name = CITIES[city_code]
        start = start_days[i]
        end = start + duration[city_code] - 1
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city_name})
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")