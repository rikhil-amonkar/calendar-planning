import z3
import json

# Define cities and their durations
cities = ['Reykjavik', 'Riga', 'Warsaw', 'Istanbul', 'Krakow']
durations = [7, 2, 3, 6, 7]  # 0: Reykjavik, 1: Riga, 2: Warsaw, 3: Istanbul, 4: Krakow

# Define allowed direct flights as pairs (city_a, city_b)
allowed_transitions = [
    (0, 2), (2, 0),  # Warsaw-Reykjavik
    (2, 3), (3, 2),  # Istanbul-Warsaw
    (3, 4), (4, 3),  # Istanbul-Krakow
    (1, 3), (3, 1),  # Riga-Istanbul
    (4, 2), (2, 4),  # Krakow-Warsaw
    (1, 2), (2, 1),  # Riga-Warsaw
]

s = z3.Solver()

# Sequence of cities to visit
seq = [z3.Int(f'seq_{i}') for i in range(5)]

# Constraints: each city is between 0 and 4, and all distinct
s.add([z3.And(0 <= seq[i], seq[i] <= 4) for i in range(5)])
s.add(z3.Distinct(seq))

# Define a Z3 function to get city duration by index
duration = z3.Function('duration', z3.IntSort(), z3.IntSort())

# Add constraints to define the duration of each city
for city_idx in range(5):
    s.add(duration(city_idx) == durations[city_idx])

# Calculate start_days for each city in the sequence
start_days = [z3.Int(f'start_day_{i}') for i in range(5)]
s.add(start_days[0] == 1)

for i in range(1, 5):
    prev_city = seq[i-1]
    s.add(start_days[i] == start_days[i-1] + duration(prev_city) - 1)

# Riga (1) must have start_day == 1
for i in range(5):
    s.add(z3.Implies(seq[i] == 1, start_days[i] == 1))

# Istanbul (3) must have start_day <= 7
for i in range(5):
    s.add(z3.Implies(seq[i] == 3, start_days[i] <= 7))

if s.check() == z3.sat:
    m = s.model()
    seq_values = [m.evaluate(seq[i]).as_long() for i in range(5)]
    start_day_values = [m.evaluate(start_days[i]).as_long() for i in range(5)]
    itinerary = []
    for i in range(5):
        city_name = cities[seq_values[i]]
        start = start_day_values[i]
        duration_city = durations[seq_values[i]]  # Now safe to use concrete index
        end = start + duration_city - 1
        day_range = f"Day {start}-Day {end}"
        itinerary.append({"day_range": day_range, "place": city_name})
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")