import z3

# Define cities and their required days
cities = ['Stuttgart', 'Istanbul', 'Vilnius', 'Seville', 'Geneva', 'Valencia', 'Munich', 'Reykjavik']
required_days = [4, 4, 4, 3, 5, 5, 3, 4]

# Define allowed flights (directed)
allowed_flights = [
    (4, 1), (1, 4), (7, 6), (6, 7), (0, 5), (5, 0), (7, 0),
    (0, 1), (1, 0), (6, 4), (4, 6), (1, 2), (2, 1), (5, 3),
    (3, 5), (5, 1), (1, 5), (2, 6), (3, 6), (6, 3), (6, 1),
    (1, 6), (5, 4), (4, 5), (5, 6), (6, 5)
]

# Initialize solver
s = z3.Solver()

# Sequence variables for 8 cities
c = [z3.Int(f'c_{i}') for i in range(8)]
entry = [z3.Int(f'entry_{i}') for i in range(8)]
exit_ = [z3.Int(f'exit_{i}') for i in range(8)]

# Each city visited exactly once
s.add(z3.Distinct(c))

# First city starts on day 1
s.add(entry[0] == 1)

# Consecutive entry days
for i in range(1, 8):
    s.add(entry[i] == exit_[i-1])

# Total trip duration
s.add(exit_[7] == 25)

# Fixed date constraints
for i in range(8):
    city = c[i]
    s.add(z3.If(city == 0, z3.And(entry[i] == 4, exit_[i] == 7),  # Stuttgart
            z3.If(city == 6, z3.And(entry[i] == 13, exit_[i] == 15),  # Munich
                    z3.If(city == 1, z3.And(entry[i] == 19, exit_[i] == 22),  # Istanbul
                            z3.If(city == 7, z3.And(entry[i] == 1, exit_[i] == 4),  # Reykjavik
                                    exit_[i] == entry[i] + required_days[city] - 1)))))

# Flight connectivity constraints
for i in range(7):
    s.add(z3.Or([z3.And(c[i] == a, c[i+1] == b) for (a, b) in allowed_flights]))

# Solve and output
if s.check() == z3.sat:
    model = s.model()
    order = [model.eval(c[i]).as_long() for i in range(8)]
    entry_days = [model.eval(entry[i]).as_long() for i in range(8)]
    exit_days = [model.eval(exit_[i]).as_long() for i in range(8)]
    
    print("Valid trip plan:")
    for i in range(8):
        city_idx = order[i]
        print(f"{cities[city_idx]}: Day {entry_days[i]} to {exit_days[i]}")
else:
    print("No valid trip plan found")