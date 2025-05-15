import z3

cities = ['Split', 'Santorini', 'London']
required_days = [6, 7, 7]

allowed_flights = [
    (0, 2), (2, 0),  # Split <-> London
    (2, 1), (1, 2)   # London <-> Santorini
]

s = z3.Solver()

# City visit order variables
c = [z3.Int(f'c_{i}') for i in range(3)]
entry = [z3.Int(f'entry_{i}') for i in range(3)]
exit_ = [z3.Int(f'exit_{i}') for i in range(3)]

# All cities must be visited exactly once
s.add(z3.Distinct(c))

# Santorini must be the last city (third position)
s.add(c[2] == 1)
# Santorini's visit must cover days 12-18
s.add(entry[2] == 12, exit_[2] == 18)

# Define entry/exit relationships and required days
for i in range(3):
    s.add(exit_[i] == entry[i] + required_days[c[i]] - 1)

# Entry of next city matches exit of previous
for i in range(1, 3):
    s.add(entry[i] == exit_[i-1])

# Flight connections between consecutive cities
for i in range(2):
    current = c[i]
    next_c = c[i+1]
    s.add(z3.Or([z3.And(current == a, next_c == b) for (a, b) in allowed_flights]))

# First city starts at day 1 or later
s.add(entry[0] >= 1)

if s.check() == z3.sat:
    model = s.model()
    order = [model.eval(c[i]).as_long() for i in range(3)]
    print("Valid trip plan:")
    for i in range(3):
        city_idx = order[i]
        start = model.eval(entry[i]).as_long()
        end = model.eval(exit_[i]).as_long()
        print(f"{cities[city_idx]}: Day {start} to {end}")
else:
    print("No valid trip plan found")