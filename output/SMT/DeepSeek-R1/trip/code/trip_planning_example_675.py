import z3

cities = ['Dubrovnik', 'Split', 'Milan', 'Porto', 'Krakow', 'Munich']
required_days = [4, 3, 3, 4, 2, 5]

allowed_flights = [
    (5,3), (3,5), (1,2), (2,1), (2,3), (3,2),
    (5,4), (4,5), (5,2), (2,5), (0,5), (5,0),
    (4,1), (1,4), (4,2), (2,4), (5,1), (1,5)
]

s = z3.Solver()

# City visit order variables
c = [z3.Int(f'c_{i}') for i in range(6)]
entry = [z3.Int(f'entry_{i}') for i in range(6)]
exit_ = [z3.Int(f'exit_{i}') for i in range(6)]

# All cities must be visited exactly once
s.add(z3.Distinct(c))

# Define entry/exit relationships and required days
for i in range(6):
    s.add(exit_[i] == entry[i] + required_days[c[i]] - 1)

# Entry of next city matches exit of previous
for i in range(1, 6):
    s.add(entry[i] == exit_[i-1])

# Flight connections between consecutive cities
for i in range(5):
    current = c[i]
    next_c = c[i+1]
    s.add(z3.Or([z3.And(current == a, next_c == b) for (a, b) in allowed_flights]))

# Fixed constraints for specific cities
for i in range(6):
    # Munich (5) must be from day 4 to 8
    s.add(z3.Implies(c[i] == 5, entry[i] == 4))
    s.add(z3.Implies(c[i] == 5, exit_[i] == 8))
    # Krakow (4) must be from day 8 to 9
    s.add(z3.Implies(c[i] == 4, entry[i] == 8))
    s.add(z3.Implies(c[i] == 4, exit_[i] == 9))
    # Milan (2) must be from day 11 to 13
    s.add(z3.Implies(c[i] == 2, entry[i] == 11))
    s.add(z3.Implies(c[i] == 2, exit_[i] == 13))

# Total trip must end on day 16
s.add(exit_[5] == 16)

# First city starts at day 1 or later
s.add(entry[0] >= 1)

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