import z3

# Define cities and their required days
cities = ['Stuttgart', 'Edinburgh', 'Athens', 'Split', 'Krakow', 'Venice', 'Mykonos']
required_days = [3, 4, 4, 2, 4, 5, 4]

# Assign city IDs
Stuttgart, Edinburgh, Athens, Split, Krakow, Venice, Mykonos = range(7)

# Define allowed flights (bidirectional)
allowed_flights = [
    (Krakow, Split), (Split, Krakow),
    (Split, Athens), (Athens, Split),
    (Edinburgh, Krakow), (Krakow, Edinburgh),
    (Venice, Stuttgart), (Stuttgart, Venice),
    (Krakow, Stuttgart), (Stuttgart, Krakow),
    (Edinburgh, Stuttgart), (Stuttgart, Edinburgh),
    (Stuttgart, Athens), (Athens, Stuttgart),
    (Venice, Edinburgh), (Edinburgh, Venice),
    (Athens, Mykonos), (Mykonos, Athens),
    (Venice, Athens), (Athens, Venice),
    (Stuttgart, Split), (Split, Stuttgart),
    (Edinburgh, Athens), (Athens, Edinburgh)
]

# Initialize solver
s = z3.Solver()

# Sequence variables
c = [z3.Int(f'c{i}') for i in range(7)]
entry = [z3.Int(f'entry{i}') for i in range(7)]
exit_ = [z3.Int(f'exit{i}') for i in range(7)]

# Each city visited exactly once
s.add(z3.Distinct(c))

# Fixed date constraints
for i in range(7):
    current = c[i]
    # Krakow: days 8-11
    s.add(z3.Implies(current == Krakow, z3.And(entry[i] == 8, exit_[i] == 11)))
    # Stuttgart: days 11-13
    s.add(z3.Implies(current == Stuttgart, z3.And(entry[i] == 11, exit_[i] == 13)))
    # Split: days 13-14
    s.add(z3.Implies(current == Split, z3.And(entry[i] == 13, exit_[i] == 14)))

# Required days calculation
for i in range(7):
    current = c[i]
    req = z3.If(current == Stuttgart, 3,
            z3.If(current == Edinburgh, 4,
                z3.If(current == Athens, 4,
                    z3.If(current == Split, 2,
                        z3.If(current == Krakow, 4,
                            z3.If(current == Venice, 5, 4))))))
    s.add(exit_[i] == entry[i] + req - 1)

# Consecutive entry days alignment
for i in range(6):
    s.add(entry[i+1] == exit_[i])

# Flight connectivity constraints
for i in range(6):
    current = c[i]
    next_c = c[i+1]
    s.add(z3.Or([z3.And(current == a, next_c == b) for (a, b) in allowed_flights]))

# Total duration constraints
s.add(entry[0] == 1)
s.add(exit_[6] == 20)

# Solve and output
if s.check() == z3.sat:
    m = s.model()
    order = [m.eval(c[i]).as_long() for i in range(7)]
    entry_days = [m.eval(entry[i]).as_long() for i in range(7)]
    exit_days = [m.eval(exit_[i]).as_long() for i in range(7)]
    
    print("Valid trip plan:")
    for i in range(7):
        print(f"{cities[order[i]]}: Day {entry_days[i]} to {exit_days[i]}")
else:
    print("No valid trip plan found")