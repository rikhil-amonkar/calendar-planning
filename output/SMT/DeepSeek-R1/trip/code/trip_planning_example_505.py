import z3

# Define cities and their required days
cities = ['Prague', 'Stuttgart', 'Split', 'Krakow', 'Florence']
required_days = [4, 2, 2, 2, 2]

# Assign city IDs
Prague, Stuttgart, Split, Krakow, Florence = range(5)

# Define allowed flights (bidirectional)
allowed_flights = [
    (Stuttgart, Split), (Split, Stuttgart),
    (Prague, Florence), (Florence, Prague),
    (Krakow, Stuttgart), (Stuttgart, Krakow),
    (Krakow, Split), (Split, Krakow),
    (Split, Prague), (Prague, Split),
    (Krakow, Prague), (Prague, Krakow)
]

# Initialize solver
s = z3.Solver()

# Sequence variables for 5 cities
c = [z3.Int(f'c{i}') for i in range(5)]
entry = [z3.Int(f'entry{i}') for i in range(5)]
exit_ = [z3.Int(f'exit{i}') for i in range(5)]

# Each city visited exactly once
s.add(z3.Distinct(c))

# Fixed constraints for Stuttgart and Split
for i in range(5):
    current = c[i]
    s.add(z3.Implies(current == Stuttgart, z3.And(entry[i] == 2, exit_[i] == 3))
    s.add(z3.Implies(current == Split, z3.And(entry[i] == 3, exit_[i] == 4))

# Duration constraints for other cities
for i in range(5):
    current = c[i]
    s.add(z3.Implies(z3.And(current != Stuttgart, current != Split),
                     exit_[i] == entry[i] + required_days[current] - 1))

# Consecutive entry days alignment
for i in range(4):
    s.add(entry[i+1] == exit_[i])

# Flight connectivity constraints between consecutive cities
for i in range(4):
    current = c[i]
    next_c = c[i+1]
    s.add(z3.Or([z3.And(current == a, next_c == b) for (a, b) in allowed_flights]))

# Total trip duration constraints
s.add(entry[0] == 1)
s.add(exit_[4] == 8)

# Solve and output
if s.check() == z3.sat:
    m = s.model()
    order = [m.eval(c[i]).as_long() for i in range(5)]
    entry_days = [m.eval(entry[i]).as_long() for i in range(5)]
    exit_days = [m.eval(exit_[i]).as_long() for i in range(5)]
    
    print("Valid trip plan:")
    for i in range(5):
        print(f"{cities[order[i]]}: Day {entry_days[i]} to {exit_days[i]}")
else:
    print("No valid trip plan found")