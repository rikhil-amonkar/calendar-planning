import z3

cities = ['Helsinki', 'Warsaw', 'Madrid', 'Split', 'Reykjavik', 'Budapest']
required_days = [2, 3, 4, 4, 2, 4]

allowed_flights = [
    (0,4), (4,0), (5,1), (1,5), (2,3), (3,2),
    (0,3), (3,0), (0,2), (2,0), (0,5), (5,0),
    (4,1), (1,4), (0,1), (1,0), (2,5), (5,2),
    (5,4), (4,5), (2,1), (1,2), (1,3), (3,1),
    (4,2)
]

s = z3.Solver()

c = [z3.Int(f'c_{i}') for i in range(6)]
entry = [z3.Int(f'entry_{i}') for i in range(6)]
exit_ = [z3.Int(f'exit_{i}') for i in range(6)]

s.add(z3.Distinct(c))
s.add(c[0] == 0)  # First city is Helsinki
s.add(entry[0] == 1, exit_[0] == 2)  # Helsinki constraints

for i in range(6):
    s.add(exit_[i] == entry[i] + required_days[c[i]] - 1)

for i in range(1, 6):
    s.add(entry[i] == exit_[i-1])

for i in range(5):
    current, next_c = c[i], c[i+1]
    s.add(z3.Or([z3.And(current == a, next_c == b) for (a, b) in allowed_flights]))

for i in range(6):
    s.add(z3.Implies(c[i] == 1, z3.And(entry[i] == 9, exit_[i] == 11)))  # Warsaw
    s.add(z3.Implies(c[i] == 4, z3.And(entry[i] == 8, exit_[i] == 9)))   # Reykjavik

for i in range(5):
    s.add(z3.Implies(c[i] == 4, c[i+1] == 1))  # Reykjavik followed by Warsaw

s.add(exit_[5] == 14)  # Total trip days

if s.check() == z3.sat:
    model = s.model()
    order = [model.eval(c[i]).as_long() for i in range(6)]
    print("Valid trip plan:")
    for i in range(6):
        city_idx = order[i]
        start = model.eval(entry[i]).as_long()
        end = model.eval(exit_[i]).as_long()
        print(f"{cities[city_idx]}: Day {start} to {end}")
else:
    print("No valid trip plan found")