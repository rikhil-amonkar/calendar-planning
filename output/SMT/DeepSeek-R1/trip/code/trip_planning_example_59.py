import z3

# Define cities and their required days
cities = ['Bucharest', 'Lyon', 'Porto']
required_days = [7, 7, 4]
Bucharest, Lyon, Porto = 0, 1, 2

# Define allowed flights (directed)
allowed_flights = [
    (Bucharest, Lyon), (Lyon, Bucharest),
    (Lyon, Porto), (Porto, Lyon)
]

# Initialize solver
s = z3.Solver()

# Sequence variables for 3 cities
c = [z3.Int(f'c{i}') for i in range(3)]
entry = [z3.Int(f'entry{i}') for i in range(3)]
exit_ = [z3.Int(f'exit{i}') for i in range(3)]

# Each city visited exactly once
s.add(z3.Distinct(c))

# Fixed constraints for Bucharest (days 1-7)
s.add(c[0] == Bucharest)
s.add(entry[0] == 1)
s.add(exit_[0] == 7)

# Lyon must come next with 7 days
s.add(entry[1] == exit_[0])  # Start immediately after Bucharest
s.add(c[1] == Lyon)
s.add(exit_[1] == entry[1] + 6)  # 7 days duration

# Porto must be last with 4 days
s.add(entry[2] == exit_[1])  # Start after Lyon
s.add(c[2] == Porto)
s.add(exit_[2] == entry[2] + 3)  # 4 days duration

# Flight connectivity constraints
s.add(z3.Or(c[0] == Bucharest, c[1] == Lyon))  # First flight Bucharest->Lyon
s.add(z3.Or(c[1] == Lyon, c[2] == Porto))      # Second flight Lyon->Porto

# Total trip duration
s.add(exit_[2] == 16)

# Solve and output
if s.check() == z3.sat:
    m = s.model()
    order = [m.eval(c[i]).as_long() for i in range(3)]
    entry_days = [m.eval(entry[i]).as_long() for i in range(3)]
    exit_days = [m.eval(exit_[i]).as_long() for i in range(3)]
    
    print("Valid trip plan:")
    for i in range(3):
        print(f"{cities[order[i]]}: Day {entry_days[i]} to {exit_days[i]}")
else:
    print("No valid trip plan found")