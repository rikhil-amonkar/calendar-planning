import z3

# Define cities and their required days (indices: 0-Stuttgart, 1-Manchester, 2-Seville)
cities = ['Stuttgart', 'Manchester', 'Seville']
required_days = [6, 4, 7]
allowed_flights = [(0,1), (1,0), (1,2), (2,1)]

# Initialize solver
s = z3.Solver()

# Sequence variables for 3 cities
c = [z3.Int(f'c_{i}') for i in range(3)]
entry = [z3.Int(f'entry_{i}') for i in range(3)]
exit_ = [z3.Int(f'exit_{i}') for i in range(3)]

# All cities visited exactly once
s.add(z3.Distinct(c))

# Stuttgart must be visited from day 1 to 6 (6 days total)
for i in range(3):
    s.add(z3.If(c[i] == 0, z3.And(entry[i] == 1, exit_[i] == 6), True))

# Duration constraints for other cities
for i in range(3):
    city = c[i]
    s.add(z3.If(city != 0, exit_[i] == entry[i] + required_days[city] - 1, True))

# Consecutive entry days follow previous exit
for i in range(1, 3):
    s.add(entry[i] == exit_[i-1])

# Flight connectivity between consecutive cities
for i in range(2):
    s.add(z3.Or([z3.And(c[i] == a, c[i+1] == b) for (a, b) in allowed_flights]))

# Total trip duration must be 15 days
s.add(exit_[2] == 15)

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