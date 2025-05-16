import z3

cities = ['Zurich', 'Bucharest', 'Hamburg', 'Barcelona', 'Reykjavik', 'Stuttgart', 'Stockholm', 'Tallinn', 'Milan', 'London']
required_days = [2, 2, 5, 4, 5, 5, 2, 4, 5, 3]

allowed_flights = [
    (9,2), (2,9), (9,4), (4,9), (8,3), (3,8), (4,3), (3,4), (4,5),
    (6,4), (4,6), (9,5), (5,9), (8,0), (0,8), (9,3), (3,9), (6,2),
    (2,6), (0,3), (3,0), (6,5), (5,6), (8,2), (2,8), (6,7), (7,6),
    (2,1), (1,2), (9,1), (1,9), (8,6), (6,8), (5,2), (2,5), (9,0),
    (0,9), (8,4), (4,8), (9,6), (6,9), (8,5), (5,8), (6,3), (3,6),
    (9,8), (8,9), (0,2), (2,0), (1,3), (3,1), (0,6), (6,0), (3,7),
    (7,3), (0,7), (7,0), (2,3), (3,2), (5,3), (3,5), (0,4), (4,0), (0,1), (1,0)
]

s = z3.Solver()

# City visit order variables
c = [z3.Int(f'c_{i}') for i in range(10)]
entry = [z3.Int(f'entry_{i}') for i in range(10)]
exit_ = [z3.Int(f'exit_{i}') for i in range(10)]

# All cities must be visited exactly once
s.add(z3.Distinct(c))

# Define entry/exit relationships and required days
for i in range(10):
    s.add(exit_[i] == entry[i] + required_days[c[i]] - 1)

# Entry of next city matches exit of previous
for i in range(1, 10):
    s.add(entry[i] == exit_[i-1])

# Flight connections between consecutive cities
for i in range(9):
    current = c[i]
    next_c = c[i+1]
    s.add(z3.Or([z3.And(current == a, next_c == b) for (a, b) in allowed_flights]))

# Fixed date constraints
for i in range(10):
    s.add(z3.Implies(c[i] == 9, z3.And(entry[i] == 1, exit_[i] == 3)))   # London
    s.add(z3.Implies(c[i] == 8, z3.And(entry[i] == 3, exit_[i] == 7)))   # Milan
    s.add(z3.Implies(c[i] == 0, z3.And(entry[i] == 7, exit_[i] == 8)))   # Zurich
    s.add(z3.Implies(c[i] == 4, z3.And(entry[i] == 9, exit_[i] == 13)))  # Reykjavik

# Total trip must end on day 28
s.add(exit_[9] == 28)

if s.check() == z3.sat:
    model = s.model()
    order = [model.eval(c[i]).as_long() for i in range(10)]
    print("Valid trip plan:")
    for i in range(10):
        city_idx = order[i]
        start = model.eval(entry[i]).as_long()
        end = model.eval(exit_[i]).as_long()
        print(f"{cities[city_idx]}: Day {start} to {end}")
else:
    print("No valid trip plan found")