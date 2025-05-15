import z3

cities = ['Paris', 'Warsaw', 'Krakow', 'Tallinn', 'Riga', 'Copenhagen', 'Helsinki', 'Oslo', 'Santorini', 'Lyon']
required_days = [5, 2, 2, 2, 2, 5, 5, 5, 2, 4]

allowed_flights = [
    (1,4), (4,1), (1,3), (3,1), (5,6), (6,5), (9,0), (0,9), (5,1), (1,5),
    (9,7), (7,9), (0,7), (7,0), (0,4), (4,0), (2,6), (6,2), (0,3), (3,0),
    (7,4), (4,7), (2,1), (1,2), (0,6), (6,0), (5,8), (8,5), (6,1), (1,6),
    (6,4), (4,6), (5,2), (2,5), (5,4), (4,5), (0,2), (2,0), (5,7), (7,5),
    (7,3), (3,7), (7,6), (6,7), (5,3), (3,5), (7,2), (2,7), (4,3), (6,3),
    (3,6), (0,5), (5,0), (0,1), (1,0), (8,7), (7,1), (1,7)
]

s = z3.Solver()

c = [z3.Int(f'c_{i}') for i in range(10)]
entry = [z3.Int(f'entry_{i}') for i in range(10)]
exit_ = [z3.Int(f'exit_{i}') for i in range(10)]

s.add(z3.Distinct(c))

for i in range(10):
    s.add(exit_[i] == entry[i] + required_days[c[i]] - 1)
    s.add(z3.Implies(c[i] == 0, z3.And(entry[i] == 4, exit_[i] == 8)))   # Paris
    s.add(z3.Implies(c[i] == 2, z3.And(entry[i] == 17, exit_[i] == 18))) # Krakow
    s.add(z3.Implies(c[i] == 6, z3.And(entry[i] == 18, exit_[i] == 22))) # Helsinki
    s.add(z3.Implies(c[i] == 4, z3.And(entry[i] == 23, exit_[i] == 24))) # Riga
    s.add(z3.Implies(c[i] == 8, z3.And(entry[i] == 12, exit_[i] == 13))) # Santorini

s.add(entry[0] == 1)
for i in range(9):
    s.add(entry[i+1] == exit_[i])

for i in range(9):
    current, next_c = c[i], c[i+1]
    s.add(z3.Or([z3.And(current == a, next_c == b) for (a, b) in allowed_flights]))

s.add(exit_[9] == 25)

if s.check() == z3.sat:
    model = s.model()
    order = [model.eval(c[i]) for i in range(10)]
    schedule = [(cities[order[i].as_long()], model.eval(entry[i]).as_long(), model.eval(exit_[i]).as_long()) for i in range(10)]
    print("Valid trip plan:")
    for city, start, end in schedule:
        print(f"{city}: Day {start} to {end}")
else:
    print("No valid trip plan found")