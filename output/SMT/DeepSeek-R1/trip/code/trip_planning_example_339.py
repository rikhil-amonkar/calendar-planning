import z3

# Define cities and their required days
cities = ['Warsaw', 'Budapest', 'Paris', 'Riga']
required_days = [2, 7, 4, 7]
allowed_flights = [(0,1), (1,0), (0,3), (3,0), (1,2), (2,1), (0,2), (2,0), (2,3), (3,2)]

# Initialize solver
s = z3.Solver()

# Sequence variables for 4 cities
c = [z3.Int(f'c_{i}') for i in range(4)]
entry = [z3.Int(f'entry_{i}') for i in range(4)]
exit_ = [z3.Int(f'exit_{i}') for i in range(4)]

# All cities visited exactly once
s.add(z3.Distinct(c))

# Fixed first and last cities (Warsaw and Riga)
s.add(c[0] == 0)
s.add(c[3] == 3)

# Entry and exit constraints for Warsaw (day 1-2) and Riga (day 11-17)
s.add(entry[0] == 1)
s.add(exit_[0] == 2)
s.add(entry[3] == 11)
s.add(exit_[3] == 17)

# Consecutive entry days
for i in range(1, 4):
    s.add(entry[i] == exit_[i-1])

# Duration constraints for Budapest and Paris (middle cities)
for i in [1, 2]:
    s.add(exit_[i] == entry[i] + z3.If(c[i] == 1, 7, 4) - 1)

# Flight connectivity between consecutive cities
for i in range(3):
    s.add(z3.Or([z3.And(c[i] == a, c[i+1] == b) for (a, b) in allowed_flights]))

# Solve and output
if s.check() == z3.sat:
    model = s.model()
    order = [model.eval(c[i]).as_long() for i in range(4)]
    entry_days = [model.eval(entry[i]).as_long() for i in range(4)]
    exit_days = [model.eval(exit_[i]).as_long() for i in range(4)]
    
    print("Valid trip plan:")
    for i in range(4):
        print(f"{cities[order[i]]}: Day {entry_days[i]} to {exit_days[i]}")
else:
    print("No valid trip plan found")