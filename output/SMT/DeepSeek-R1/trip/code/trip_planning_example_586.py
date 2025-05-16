import z3

# Define cities and their required days
cities = ['Prague', 'Helsinki', 'Frankfurt', 'Naples', 'Lyon']
required_days = [2, 4, 3, 4, 3]

# Assign city IDs
Prague, Helsinki, Frankfurt, Naples, Lyon = range(5)

# Define allowed flights (bidirectional)
allowed_flights = [
    (Prague, Lyon), (Lyon, Prague),
    (Prague, Frankfurt), (Frankfurt, Prague),
    (Frankfurt, Lyon), (Lyon, Frankfurt),
    (Helsinki, Naples), (Naples, Helsinki),
    (Helsinki, Frankfurt), (Frankfurt, Helsinki),
    (Naples, Frankfurt), (Frankfurt, Naples),
    (Prague, Helsinki), (Helsinki, Prague)
]

# Initialize solver
s = z3.Solver()

# Sequence variables for 5 cities
c = [z3.Int(f'c{i}') for i in range(5)]
entry = [z3.Int(f'entry{i}') for i in range(5)]
exit_ = [z3.Int(f'exit{i}') for i in range(5)]

# Each city visited exactly once
s.add(z3.Distinct(c))

# Fixed constraints for Prague and Helsinki
s.add(c[0] == Prague)
s.add(entry[0] == 1)
s.add(exit_[0] == 2)  # Prague: 1 + 2 - 1 = 2

s.add(c[1] == Helsinki)
s.add(entry[1] == 2)
s.add(exit_[1] == 5)  # Helsinki: 2 + 4 - 1 = 5

# Entry-exit relationships for remaining cities
for i in range(2, 5):
    current = c[i]
    req = z3.If(current == Prague, 2,
            z3.If(current == Helsinki, 4,
                z3.If(current == Frankfurt, 3,
                    z3.If(current == Naples, 4, 3))))
    s.add(exit_[i] == entry[i] + req - 1)

# Consecutive entry days alignment
for i in range(4):
    s.add(entry[i+1] == exit_[i])

# Flight connectivity constraints between consecutive cities
for i in range(4):
    current = c[i]
    next_c = c[i+1]
    s.add(z3.Or([z3.And(current == a, next_c == b) for (a, b) in allowed_flights]))

# Total trip duration must be 12 days
s.add(exit_[4] == 12)

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