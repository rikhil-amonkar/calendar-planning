import z3

# Define cities and their required days
cities = ['London', 'Oslo', 'Split', 'Porto']
required_days = [7, 2, 5, 5]
allowed_flights = [(0,1), (1,0), (2,1), (1,2), (1,3), (3,1), (0,2), (2,0)]

# Initialize solver
s = z3.Solver()

# Sequence variables for 4 cities
c = [z3.Int(f'c_{i}') for i in range(4)]
entry = [z3.Int(f'entry_{i}') for i in range(4)]
exit_ = [z3.Int(f'exit_{i}') for i in range(4)]

# All cities visited exactly once and first city is London
s.add(z3.Distinct(c))
s.add(c[0] == 0)

# London's fixed schedule (days 1-7)
s.add(entry[0] == 1)
s.add(exit_[0] == 7)

# Split's fixed schedule (days 7-11) and other cities' duration constraints
for i in range(4):
    s.add(z3.If(c[i] == 2,  # Split
                z3.And(entry[i] == 7, exit_[i] == 11),
                exit_[i] == entry[i] + required_days[c[i]] - 1))

# Consecutive entry days must follow previous city's exit
for i in range(1, 4):
    s.add(entry[i] == exit_[i-1])

# Flight connectivity between consecutive cities
for i in range(3):
    s.add(z3.Or([z3.And(c[i] == a, c[i+1] == b) for (a, b) in allowed_flights]))

# Total trip duration must be 16 days
s.add(exit_[3] == 16)

# Solve and output
if s.check() == z3.sat:
    model = s.model()
    order = [model.eval(c[i]).as_long() for i in range(4)]
    entry_days = [model.eval(entry[i]).as_long() for i in range(4)]
    exit_days = [model.eval(exit_[i]).as_long() for i in range(4)]
    
    print("Valid trip plan:")
    for i in range(4):
        city_idx = order[i]
        print(f"{cities[city_idx]}: Day {entry_days[i]} to {exit_days[i]}")
else:
    print("No valid trip plan found")