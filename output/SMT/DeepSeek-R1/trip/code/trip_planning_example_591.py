import z3

# Define cities and their required days (indices: 0-Stuttgart, 1-Bucharest, 2-Geneva, 3-Valencia, 4-Munich)
cities = ['Stuttgart', 'Bucharest', 'Geneva', 'Valencia', 'Munich']
required_days = [2, 2, 4, 6, 7]
allowed_flights = [
    (2,4), (4,2), (4,3), (3,4), (1,3), (3,1),
    (4,1), (1,4), (3,0), (0,3), (2,3), (3,2)
]

# Initialize solver
s = z3.Solver()

# Sequence variables for 5 cities
c = [z3.Int(f'c_{i}') for i in range(5)]
entry = [z3.Int(f'entry_{i}') for i in range(5)]
exit_ = [z3.Int(f'exit_{i}') for i in range(5)]

# All cities visited exactly once
s.add(z3.Distinct(c))

# Geneva must be first city (days 1-4)
s.add(c[0] == 2)
s.add(entry[0] == 1)
s.add(exit_[0] == 4)

# Munich must be second city (days 4-10)
s.add(c[1] == 4)
s.add(entry[1] == 4)
s.add(exit_[1] == 10)

# Duration constraints for remaining cities
for i in range(2, 5):
    s.add(exit_[i] == entry[i] + required_days[c[i]] - 1)

# Consecutive entry days follow previous exit
for i in range(1, 5):
    s.add(entry[i] == exit_[i-1])

# Flight connectivity between consecutive cities
for i in range(4):
    s.add(z3.Or([z3.And(c[i] == a, c[i+1] == b) for (a, b) in allowed_flights]))

# Total trip duration must be 17 days
s.add(exit_[4] == 17)

# Solve and output
if s.check() == z3.sat:
    model = s.model()
    order = [model.eval(c[i]).as_long() for i in range(5)]
    entry_days = [model.eval(entry[i]).as_long() for i in range(5)]
    exit_days = [model.eval(exit_[i]).as_long() for i in range(5)]
    
    print("Valid trip plan:")
    for i in range(5):
        city_idx = order[i]
        print(f"{cities[city_idx]}: Day {entry_days[i]} to {exit_days[i]}")
else:
    print("No valid trip plan found")