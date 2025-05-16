import z3

# Define cities and their required days
cities = ['Venice', 'Barcelona', 'Copenhagen', 'Lyon', 'Reykjavik', 'Dubrovnik', 'Athens', 'Tallinn', 'Munich']
required_days = [4, 3, 4, 4, 4, 5, 2, 5, 3]
Barcelona_idx = 1
Copenhagen_idx = 2
Dubrovnik_idx = 5

# Define allowed flights (directed)
allowed_flights = [
    (2,6), (6,2), (2,5), (5,2), (8,7), (7,8), (2,8), (8,2), (0,8), (8,0),
    (4,6), (6,5), (5,6), (0,6), (6,0), (3,1), (1,3), (2,4), (4,2), (4,8),
    (8,4), (6,8), (8,6), (3,8), (8,3), (1,4), (4,1), (0,2), (2,0), (1,5),
    (5,1), (3,0), (0,3), (5,8), (8,5), (1,6), (6,1), (2,1), (1,2), (0,1),
    (1,0), (1,8), (8,1), (1,7), (7,1), (2,7), (7,2)
]

# Initialize solver
s = z3.Solver()

# Sequence variables for 9 cities
c = [z3.Int(f'c_{i}') for i in range(9)]
entry = [z3.Int(f'entry_{i}') for i in range(9)]
exit_ = [z3.Int(f'exit_{i}') for i in range(9)]

# Each city visited exactly once
s.add(z3.Distinct(c))

# First city starts on day 1
s.add(entry[0] == 1)

# Consecutive entry days
for i in range(1, 9):
    s.add(entry[i] == exit_[i-1])

# Total trip duration constraint
s.add(exit_[8] == 26)

# City-specific constraints
for i in range(9):
    city = c[i]
    s.add(z3.If(
        city == Barcelona_idx,
        z3.And(entry[i] == 10, exit_[i] == 12),
        z3.If(
            city == Copenhagen_idx,
            z3.And(entry[i] == 7, exit_[i] == 10),
            z3.If(
                city == Dubrovnik_idx,
                z3.And(entry[i] == 16, exit_[i] == 20),
                exit_[i] == entry[i] + (required_days[city] - 1)
            )
        )
    ))

# Flight connectivity constraints
for i in range(8):
    s.add(z3.Or([z3.And(c[i] == a, c[i+1] == b) for (a, b) in allowed_flights]))

# Solve and output
if s.check() == z3.sat:
    model = s.model()
    order = [model.eval(c[i]).as_long() for i in range(9)]
    entry_days = [model.eval(entry[i]).as_long() for i in range(9)]
    exit_days = [model.eval(exit_[i]).as_long() for i in range(9)]
    
    print("Valid trip plan:")
    for i in range(9):
        city_idx = order[i]
        print(f"{cities[city_idx]}: Day {entry_days[i]} to {exit_days[i]}")
else:
    print("No valid trip plan found")