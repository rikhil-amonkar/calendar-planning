from z3 import *

# Define city names and their integer mappings
cities = ['London', 'Milan', 'Zurich', 'Stockholm', 'Reykjavik', 'Stuttgart', 'Hamburg', 'Bucharest', 'Barcelona', 'Tallinn']
n = len(cities)

# Minimum durations for each city (in the same order as cities)
min_dur = [3, 3, 1, 1, 4, 4, 4, 1, 3, 4]

# Define edges of the travel graph (undirected)
edges = [
    (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9),
    (1, 2), (1, 5), (1, 6), (1, 8),
    (2, 5), (2, 6),
    (3, 4), (3, 9),
    (4, 9),
    (5, 6),
    (7, 8)
]

# Create Z3 solver
s = Solver()

# Sequence of cities (each element is an integer representing a city index)
seq = [Int(f'seq_{i}') for i in range(n)]

# Durations for each city in the sequence
durations = [Int(f'duration_{i}') for i in range(n)]

# Start days for each city in the sequence
starts = [Int(f'start_{i}') for i in range(n)]

# Each city index in seq must be between 0 and n-1
for i in range(n):
    s.add(And(seq[i] >= 0, seq[i] < n))

# All cities must be distinct in the sequence
s.add(Distinct(seq))

# Minimum duration constraints using Z3 array
min_dur_array = Array('min_dur_array', IntSort(), IntSort())
for idx, dur in enumerate(min_dur):
    s.add(min_dur_array[idx] == dur)

for i in range(n):
    s.add(durations[i] >= min_dur_array[seq[i]])

# Start day constraints
s.add(starts[0] == 1)
for i in range(1, n):
    s.add(starts[i] == starts[i-1] + durations[i-1])
s.add(starts[n-1] + durations[n-1] == 29)  # Since the last day is day 28

# Travel constraints: consecutive cities must be connected by an edge
for i in range(n - 1):
    city1 = seq[i]
    city2 = seq[i+1]
    edge_constraints = []
    for (a, b) in edges:
        edge_constraints.append(And(city1 == a, city2 == b))
        edge_constraints.append(And(city1 == b, city2 == a))
    s.add(Or(edge_constraints))

# Check for a solution
if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(n):
        city_idx = model.evaluate(seq[i]).as_long()
        start_day = model.evaluate(starts[i]).as_long()
        duration_val = model.evaluate(durations[i]).as_long()
        end_day = start_day + duration_val - 1
        if duration_val == 1:
            day_range = f"Day {start_day}"
        else:
            day_range = f"Day {start_day}-{end_day}"
        itinerary.append({'day_range': day_range, 'place': cities[city_idx]})
    print(f"Plan found: {itinerary}")
else:
    print("No valid plan found.")