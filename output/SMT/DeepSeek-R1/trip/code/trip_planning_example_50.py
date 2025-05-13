from z3 import *

# Define city indices
Vilnius = 0
Munich = 1
Mykonos = 2

allowed_pairs = [
    (Vilnius, Munich),
    (Munich, Mykonos),
    (Mykonos, Munich)
]

durations = {
    Vilnius: 4,
    Munich: 3,
    Mykonos: 7
}

solver = Solver()

# Sequence variables (visiting 3 cities)
s = [Int(f's_{i}') for i in range(3)]
for i in range(3):
    solver.add(s[i] >= 0, s[i] <= 2)
solver.add(Distinct(s))  # Each city visited exactly once

# Flight constraints between consecutive cities
for i in range(2):
    solver.add(Or([And(s[i] == a, s[i+1] == b) for (a, b) in allowed_pairs]))

# Start and end days
start = [Int(f'start_{i}') for i in range(3)]
end = [Int(f'end_{i}') for i in range(3)]

solver.add(start[0] == 1)  # Trip starts on day 1

for i in range(3):
    city = s[i]
    duration = durations[city]
    solver.add(end[i] == start[i] + duration - 1)
    if i < 2:
        solver.add(start[i+1] == end[i] + 1)  # Next city starts after flight day

solver.add(end[2] == 12)  # Total trip duration is 12 days

if solver.check() == sat:
    model = solver.model()
    seq = [model.evaluate(s[i]).as_long() for i in range(3)]
    start_days = [model.evaluate(start[i]).as_long() for i in range(3)]
    end_days = [model.evaluate(end[i]).as_long() for i in range(3)]
    city_names = {
        Vilnius: 'Vilnius',
        Munich: 'Munich',
        Mykonos: 'Mykonos'
    }
    print("Trip Plan:")
    for i in range(3):
        city = seq[i]
        print(f"{city_names[city]}: Day {start_days[i]} to Day {end_days[i]}")
else:
    print("No solution found")