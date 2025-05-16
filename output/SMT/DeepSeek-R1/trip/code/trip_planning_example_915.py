import z3

# Define cities and their required days (indices: 0-Bucharest, 1-Venice, 2-Prague, 3-Frankfurt, 4-Zurich, 5-Florence, 6-Tallinn)
cities = ['Bucharest', 'Venice', 'Prague', 'Frankfurt', 'Zurich', 'Florence', 'Tallinn']
required_days = [3, 5, 4, 5, 5, 5, 5]
allowed_flights = [
    (2,6), (6,2), (2,4), (4,2), (5,2), (2,5), (3,0), (0,3),
    (3,1), (1,3), (2,0), (0,2), (0,4), (4,0), (6,3), (3,6),
    (4,5), (3,4), (4,3), (4,1), (1,4), (5,3), (3,5), (2,3),
    (3,2), (6,4), (4,6)
]

# Initialize solver
s = z3.Solver()

# Sequence variables for 7 cities
c = [z3.Int(f'c_{i}') for i in range(7)]
entry = [z3.Int(f'entry_{i}') for i in range(7)]
exit_ = [z3.Int(f'exit_{i}') for i in range(7)]

# All cities visited exactly once
s.add(z3.Distinct(c))

# Constraints for fixed cities
for i in range(7):
    city = c[i]
    # Venice must be days 22-26
    s.add(z3.Implies(city == 1, z3.And(entry[i] == 22, exit_[i] == 26)))
    # Frankfurt must be days 12-16
    s.add(z3.Implies(city == 3, z3.And(entry[i] == 12, exit_[i] == 16)))
    # Tallinn must be days 8-12
    s.add(z3.Implies(city == 6, z3.And(entry[i] == 8, exit_[i] == 12)))
    # Other cities' duration constraints
    s.add(z3.Implies(z3.And(city != 1, city != 3, city != 6),
                     exit_[i] == entry[i] + required_days[city] - 1))

# Consecutive entry days follow previous exit
for i in range(6):
    s.add(entry[i+1] == exit_[i])

# Flight connectivity between consecutive cities
for i in range(6):
    current = c[i]
    next_city = c[i+1]
    s.add(z3.Or([z3.And(current == a, next_city == b) for (a, b) in allowed_flights]))

# Total trip duration must be 26 days
s.add(exit_[6] == 26)

# Solve and output
if s.check() == z3.sat:
    model = s.model()
    order = [model.eval(c[i]).as_long() for i in range(7)]
    entry_days = [model.eval(entry[i]).as_long() for i in range(7)]
    exit_days = [model.eval(exit_[i]).as_long() for i in range(7)]
    
    print("Valid trip plan:")
    for i in range(7):
        city_idx = order[i]
        print(f"{cities[city_idx]}: Day {entry_days[i]} to {exit_days[i]}")
else:
    print("No valid trip plan found")