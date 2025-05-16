import z3

# Define cities and their required days (indices: 0-Valencia, 1-Riga, 2-Prague, 3-Mykonos, 4-Zurich, 5-Bucharest, 6-Nice)
cities = ['Valencia', 'Riga', 'Prague', 'Mykonos', 'Zurich', 'Bucharest', 'Nice']
required_days = [5, 5, 3, 3, 5, 5, 2]
allowed_flights = [
    (3,6), (6,3), (3,4), (4,3), (2,5), (5,2), (0,5), (5,0),
    (4,2), (2,4), (1,6), (6,1), (4,1), (1,4), (4,5), (5,4),
    (4,0), (0,4), (5,1), (1,5), (2,1), (1,2), (2,0), (0,2),
    (4,6), (6,4)
]

# Initialize solver
s = z3.Solver()

# Sequence variables for 7 cities
c = [z3.Int(f'c_{i}') for i in range(7)]
entry = [z3.Int(f'entry_{i}') for i in range(7)]
exit_ = [z3.Int(f'exit_{i}') for i in range(7)]

# All cities visited exactly once
s.add(z3.Distinct(c))

# Mykonos must be first city (day 1-3)
s.add(c[0] == 3)
s.add(entry[0] == 1)
s.add(exit_[0] == 3)

# Prague must be scheduled from day 7 to 9
for i in range(7):
    s.add(z3.If(c[i] == 2,  # Prague
                z3.And(entry[i] == 7, exit_[i] == 9),
                True))

# Duration constraints for other cities
for i in range(7):
    s.add(z3.Or(
        c[i] == 3,  # Mykonos (already handled)
        c[i] == 2,  # Prague (already handled)
        exit_[i] == entry[i] + required_days[c[i]] - 1
    ))

# Consecutive entry days follow previous exit
for i in range(1, 7):
    s.add(entry[i] == exit_[i-1])

# Flight connectivity between consecutive cities
for i in range(6):
    s.add(z3.Or([z3.And(c[i] == a, c[i+1] == b) for (a, b) in allowed_flights]))

# Total trip duration must be 22 days
s.add(exit_[6] == 22)

# Solve and output
if s.check() == z3.sat:
    model = s.model()
    order = [model.eval(c[i]).as_long() for i in range(7)]
    entry_days = [model.eval(entry[i]).as_long() for i in range(7)]
    exit_days = [model.eval(exit_[i]).as_long() for i in range(7)]
    
    print("Valid trip plan:")
    for i in range(7):
        city_idx = order[i]
        print(f"{cities[city_idx]}: Day {entry_days[i]} to {exit_days[i]}")
else:
    print("No valid trip plan found")