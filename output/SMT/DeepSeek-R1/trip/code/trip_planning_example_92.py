import z3

# Define cities and their required days (indices: 0-Riga, 1-Vilnius, 2-Dublin)
cities = ['Riga', 'Vilnius', 'Dublin']
required_days = [5, 7, 2]
allowed_flights = [(0, 1), (0, 2), (2, 0)]  # Riga<->Dublin, Riga->Vilnius

# Initialize solver
s = z3.Solver()

# Sequence variables for 3 cities
c = [z3.Int(f'c_{i}') for i in range(3)]
entry = [z3.Int(f'entry_{i}') for i in range(3)]
exit_ = [z3.Int(f'exit_{i}') for i in range(3)]

# All cities visited exactly once
s.add(z3.Distinct(c))

# Duration constraints for each city
for i in range(3):
    city = c[i]
    for j in range(3):
        s.add(z3.Implies(city == j, exit_[i] == entry[i] + required_days[j] - 1))

# Consecutive entry days follow previous exit and first starts at day 1
s.add(entry[0] == 1)
for i in range(2):
    s.add(entry[i+1] == exit_[i])

# Flight connectivity between consecutive cities
for i in range(2):
    current = c[i]
    next_city = c[i+1]
    s.add(z3.Or([z3.And(current == a, next_city == b) for (a, b) in allowed_flights]))

# Total trip duration must be 12 days
s.add(exit_[2] == 12)

# Solve and output
if s.check() == z3.sat:
    model = s.model()
    order = [model.eval(c[i]).as_long() for i in range(3)]
    entry_days = [model.eval(entry[i]).as_long() for i in range(3)]
    exit_days = [model.eval(exit_[i]).as_long() for i in range(3)]
    
    print("Valid trip plan:")
    for i in range(3):
        city_idx = order[i]
        print(f"{cities[city_idx]}: Day {entry_days[i]} to {exit_days[i]}")
else:
    print("No valid trip plan found")