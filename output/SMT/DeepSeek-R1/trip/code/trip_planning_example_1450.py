import z3

# Define cities and their required days
cities = ['Stockholm', 'Hamburg', 'Florence', 'Istanbul', 'Oslo', 'Vilnius', 'Santorini', 'Munich', 'Frankfurt', 'Krakow']
required_days = [3, 5, 2, 5, 5, 5, 2, 5, 4, 5]
allowed_flights = [
    (4,0), (0,4), (9,8), (8,9), (9,3), (3,9), (9,5), (4,3), (3,4),
    (5,3), (3,5), (4,9), (9,4), (8,3), (3,8), (4,5), (5,4), (7,0),
    (0,7), (1,0), (0,1), (7,1), (1,7), (7,3), (3,7), (4,7), (7,4),
    (8,2), (2,8), (4,1), (1,4), (5,8), (8,5), (2,7), (9,7), (7,9),
    (1,3), (3,1), (8,0), (0,8), (0,6), (8,7), (7,8), (6,4), (9,0),
    (0,9), (5,7), (8,1), (1,8)
]

# Initialize solver
s = z3.Solver()

# Sequence variables for 10 cities
c = [z3.Int(f'c_{i}') for i in range(10)]
entry = [z3.Int(f'entry_{i}') for i in range(10)]
exit_ = [z3.Int(f'exit_{i}') for i in range(10)]

# Each city visited exactly once
s.add(z3.Distinct(c))

# First city starts on day 1
s.add(entry[0] == 1)

# Consecutive entry days
for i in range(1, 10):
    s.add(entry[i] == exit_[i-1])

# Total trip duration
s.add(exit_[9] == 32)

# City-specific constraints for Istanbul and Krakow
for i in range(10):
    city = c[i]
    istanbul = z3.And(city == 3, entry[i] == 25, exit_[i] == 29)
    krakow = z3.And(city == 9, entry[i] == 5, exit_[i] == 9)
    other = exit_[i] == entry[i] + (required_days[city] - 1)
    s.add(z3.If(city == 3, istanbul, z3.If(city == 9, krakow, other)))

# Flight connectivity constraints
for i in range(9):
    current = c[i]
    next_city = c[i+1]
    s.add(z3.Or([z3.And(current == a, next_city == b) for a, b in allowed_flights]))

# Solve and output
if s.check() == z3.sat:
    model = s.model()
    order = [model.eval(c[i]).as_long() for i in range(10)]
    entry_days = [model.eval(entry[i]).as_long() for i in range(10)]
    exit_days = [model.eval(exit_[i]).as_long() for i in range(10)]
    
    print("Valid trip plan:")
    for i in range(10):
        city_idx = order[i]
        print(f"{cities[city_idx]}: Day {entry_days[i]} to {exit_days[i]}")
else:
    print("No valid trip plan found")