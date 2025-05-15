import z3

# Define cities and their required days (indices: 0-Manchester, 1-Stuttgart, 2-Madrid, 3-Vienna)
cities = ['Manchester', 'Stuttgart', 'Madrid', 'Vienna']
required_days = [7, 5, 4, 2]
allowed_flights = [(0,1), (1,0), (0,2), (2,0), (0,3), (3,0), (1,3), (3,1), (2,3), (3,2)]

# Initialize solver
s = z3.Solver()

# Sequence variables for 4 cities
c = [z3.Int(f'c_{i}') for i in range(4)]
entry = [z3.Int(f'entry_{i}') for i in range(4)]
exit_ = [z3.Int(f'exit_{i}') for i in range(4)]

# First city must be Manchester (wedding), last must be Stuttgart (workshop)
s.add(c[0] == 0)
s.add(c[3] == 1)
s.add(z3.Distinct(c))

# Duration constraints for each city
for i in range(4):
    s.add(exit_[i] == entry[i] + required_days[c[i]] - 1)

# Entry days follow previous exit and first starts at day 1
s.add(entry[0] == 1)
for i in range(3):
    s.add(entry[i+1] == exit_[i])

# Flight connectivity between consecutive cities
for i in range(3):
    current = c[i]
    next_c = c[i+1]
    s.add(z3.Or([z3.And(current == a, next_c == b) for (a, b) in allowed_flights]))

# Total trip duration must be 15 days (Stuttgart ends on day 15)
s.add(exit_[3] == 15)

# Solve and output
if s.check() == z3.sat:
    model = s.model()
    order = [model.eval(c[i]).as_long() for i in range(4)]
    entry_days = [model.eval(entry[i]).as_long() for i in range(4)]
    exit_days = [model.eval(exit_[i]).as_long() for i in range(4)]
    
    print("Valid trip plan:")
    for i in range(4):
        city_idx = order[i]
        print(f"{cities[city_idx]}: Day {entry_days[i]} to {exit_days[i]}")
else:
    print("No valid trip plan found")