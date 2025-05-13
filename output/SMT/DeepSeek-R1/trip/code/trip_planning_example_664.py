from z3 import *

# Define city indices
Tallinn = 0
Bucharest = 1
Seville = 2
Stockholm = 3
Munich = 4
Milan = 5

allowed_pairs = [
    (Milan, Stockholm),
    (Stockholm, Milan),
    (Munich, Stockholm),
    (Stockholm, Munich),
    (Bucharest, Munich),
    (Munich, Bucharest),
    (Munich, Seville),
    (Seville, Munich),
    (Stockholm, Tallinn),
    (Tallinn, Stockholm),
    (Munich, Milan),
    (Milan, Munich),
    (Munich, Tallinn),
    (Tallinn, Munich),
    (Seville, Milan),
    (Milan, Seville)
]

durations = {
    Tallinn: 2,
    Bucharest: 4,
    Seville: 5,
    Stockholm: 5,
    Munich: 5,
    Milan: 2
}

solver = Solver()

# Sequence variables
s = [Int(f's_{i}') for i in range(6)]
for i in range(6):
    solver.add(s[i] >= 0, s[i] <= 5)
solver.add(Distinct(s))

# Flight constraints between consecutive cities
for i in range(5):
    solver.add(Or([And(s[i] == a, s[i+1] == b) for (a, b) in allowed_pairs]))

# Start and end days
start = [Int(f'start_{i}') for i in range(6)]
end = [Int(f'end_{i}') for i in range(6)]

solver.add(start[0] == 1)

for i in range(6):
    duration = durations[s[i]]
    solver.add(end[i] == start[i] + duration - 1)
    if i < 5:
        solver.add(start[i+1] == end[i])

solver.add(end[5] == 18)

# Time constraints for specific cities
for i in range(6):
    solver.add(Implies(s[i] == Bucharest, And(start[i] == 1, end[i] == 4)))
    solver.add(Implies(s[i] == Munich, And(start[i] == 4, end[i] == 8)))
    solver.add(Implies(s[i] == Seville, And(start[i] == 8, end[i] == 12)))

if solver.check() == sat:
    model = solver.model()
    seq = [model.evaluate(s[i]).as_long() for i in range(6)]
    start_days = [model.evaluate(start[i]).as_long() for i in range(6)]
    end_days = [model.evaluate(end[i]).as_long() for i in range(6)]
    city_names = {
        Tallinn: 'Tallinn',
        Bucharest: 'Bucharest',
        Seville: 'Seville',
        Stockholm: 'Stockholm',
        Munich: 'Munich',
        Milan: 'Milan'
    }
    print("Trip Plan:")
    for i in range(6):
        city = seq[i]
        print(f"{city_names[city]}: Day {start_days[i]} to Day {end_days[i]}")
else:
    print("No solution found")