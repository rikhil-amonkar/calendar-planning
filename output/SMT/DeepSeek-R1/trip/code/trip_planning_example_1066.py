import z3

# Define cities and their required days (indices: 0-Brussels, 1-Bucharest, 2-Stuttgart, 3-Mykonos, 4-Madrid, 5-Helsinki, 6-Split, 7-London)
cities = ['Brussels', 'Bucharest', 'Stuttgart', 'Mykonos', 'Madrid', 'Helsinki', 'Split', 'London']
required_days = [4, 3, 4, 2, 2, 5, 3, 5]
allowed_flights = [
    (5,7), (7,5), (6,4), (4,6), (5,4), (4,5), (7,4), (4,7),
    (0,7), (7,0), (1,7), (7,1), (0,1), (1,0), (1,4), (4,1),
    (6,5), (5,6), (3,4), (4,3), (2,7), (7,2), (5,0), (0,5),
    (0,4), (4,0), (6,7), (7,6), (2,6), (6,2), (7,3), (3,7)
]

# Initialize solver
s = z3.Solver()

# Sequence variables for 8 cities
c = [z3.Int(f'c_{i}') for i in range(8)]
entry = [z3.Int(f'entry_{i}') for i in range(8)]
exit_ = [z3.Int(f'exit_{i}') for i in range(8)]

# All cities visited exactly once
s.add(z3.Distinct(c))

# Stuttgart must be first (days 1-4) and Madrid last (days 20-21)
s.add(c[0] == 2)
s.add(entry[0] == 1)
s.add(exit_[0] == 4)
s.add(c[7] == 4)
s.add(entry[7] == 20)
s.add(exit_[7] == 21)

# Duration constraints for other cities
for i in range(8):
    city = c[i]
    s.add(z3.Implies(z3.And(city != 2, city != 4),
                     exit_[i] == entry[i] + required_days[city] - 1))

# Consecutive entry days follow previous exit
for i in range(7):
    s.add(entry[i+1] == exit_[i])

# Flight connectivity between consecutive cities
for i in range(7):
    current = c[i]
    next_city = c[i+1]
    s.add(z3.Or([z3.And(current == a, next_city == b) for (a, b) in allowed_flights]))

# Total trip duration must be 21 days
s.add(exit_[7] == 21)

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