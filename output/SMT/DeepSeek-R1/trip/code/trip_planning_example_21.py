import z3

# Define cities and their required days
cities = ['Venice', 'Mykonos', 'Vienna']
required_days = [6, 2, 4]
allowed_flights = [(1, 2), (2, 1), (2, 0), (0, 2)]

# Initialize solver
s = z3.Solver()

# Sequence variables for 3 cities
c = [z3.Int(f'c_{i}') for i in range(3)]
entry = [z3.Int(f'entry_{i}') for i in range(3)]
exit_ = [z3.Int(f'exit_{i}') for i in range(3)]

# Each city visited exactly once and Venice must be last
s.add(z3.Distinct(c))
s.add(c[2] == 0)  # Venice is the last city

# Flight connectivity constraints
for i in range(2):
    s.add(z3.Or([z3.And(c[i] == a, c[i+1] == b) for (a, b) in allowed_flights]))

# Entry day constraints
s.add(entry[0] == 1)  # Trip starts on day 1

# Venice must be scheduled from day 5 to 10
s.add(z3.Or([z3.And(c[i] == 0, entry[i] == 5, exit_[i] == 10) for i in range(3)]))

# Duration constraints for non-Venice cities
for i in range(3):
    s.add(z3.If(c[i] == 0,  # Skip duration constraint for Venice since it's fixed
                z3.And(entry[i] == 5, exit_[i] == 10),
                exit_[i] == entry[i] + required_days[c[i]] - 1))

# Consecutive entry days
for i in range(1, 3):
    s.add(entry[i] == exit_[i-1])

# Total trip duration
s.add(exit_[2] == 10)

# Solve and output
if s.check() == z3.sat:
    model = s.model()
    order = [model.eval(c[i]).as_long() for i in range(3)]
    entry_days = [model.eval(entry[i]).as_long() for i in range(3)]
    exit_days = [model.eval(exit_[i]).as_long() for i in range(3)]
    
    print("Valid trip plan:")
    for i in range(3):
        city_idx = order[i]
        print(f"{cities[city_idx]}: Day {entry_days[i]} to {exit_days[i]}")
else:
    print("No valid trip plan found")