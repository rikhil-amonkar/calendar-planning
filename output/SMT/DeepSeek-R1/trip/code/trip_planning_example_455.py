import z3

cities = ['Reykjavik', 'Riga', 'Warsaw', 'Istanbul', 'Krakow']
required_days = [7, 2, 3, 6, 7]

allowed_flights = [
    (3,4), (4,3), (2,0), (0,2), (3,2), (2,3),
    (1,3), (3,1), (4,2), (2,4), (1,2), (2,1)
]

s = z3.Solver()

# City visit order variables
c = [z3.Int(f'c_{i}') for i in range(5)]
entry = [z3.Int(f'entry_{i}') for i in range(5)]
exit_ = [z3.Int(f'exit_{i}') for i in range(5)]

# All cities must be visited exactly once
s.add(z3.Distinct(c))

# Define entry/exit relationships and required days
for i in range(5):
    s.add(exit_[i] == entry[i] + required_days[c[i]] - 1)

# Entry of next city matches exit of previous
for i in range(1, 5):
    s.add(entry[i] == exit_[i-1])

# Flight connections between consecutive cities
for i in range(4):
    current = c[i]
    next_c = c[i+1]
    s.add(z3.Or([z3.And(current == a, next_c == b) for (a, b) in allowed_flights]))

# Fixed constraints for Riga and Istanbul
for i in range(5):
    # Riga must be from day 1 to 2 (2 days)
    s.add(z3.Implies(c[i] == 1, z3.And(entry[i] == 1, exit_[i] == 2)))
    # Istanbul must include days 2-7 (6 days)
    s.add(z3.Implies(c[i] == 3, z3.And(entry[i] == 2, exit_[i] == 7)))

# Total trip must end on day 21
s.add(exit_[4] == 21)

# Ensure Riga comes before Istanbul and they are consecutive
s.add(z3.Or(
    z3.And(c[0] == 1, c[1] == 3),  # Riga first, Istanbul second
    z3.And(c[1] == 1, c[2] == 3),  # Riga second, Istanbul third (impossible due to date constraints)
    z3.And(c[2] == 1, c[3] == 3),  # Similarly invalid
    z3.And(c[3] == 1, c[4] == 3)   # Invalid
))

if s.check() == z3.sat:
    model = s.model()
    order = [model.eval(c[i]).as_long() for i in range(5)]
    print("Valid trip plan:")
    for i in range(5):
        city_idx = order[i]
        start = model.eval(entry[i]).as_long()
        end = model.eval(exit_[i]).as_long()
        print(f"{cities[city_idx]}: Day {start} to {end}")
else:
    print("No valid trip plan found")