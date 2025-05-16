import z3

# Define cities and their required days
cities = ['Riga', 'Amsterdam', 'Mykonos']
required_days = [2, 2, 5]
Riga, Amsterdam, Mykonos = 0, 1, 2

# Define allowed flights (directed)
allowed_flights = [
    (Amsterdam, Mykonos), (Mykonos, Amsterdam),
    (Riga, Amsterdam), (Amsterdam, Riga)
]

# Initialize solver
s = z3.Solver()

# Sequence variables for 3 cities
c = [z3.Int(f'c{i}') for i in range(3)]
entry = [z3.Int(f'entry{i}') for i in range(3)]
exit_ = [z3.Int(f'exit{i}') for i in range(3)]

# Each city visited exactly once
s.add(z3.Distinct(c))

# First city must be Riga with fixed days 1-2
s.add(c[0] == Riga)
s.add(entry[0] == 1)
s.add(exit_[0] == 2)

# Entry days alignment and duration constraints
for i in range(1, 3):
    s.add(entry[i] == exit_[i-1])  # Consecutive entry days
    
    # Duration constraints based on city
    current_city = c[i]
    s.add(z3.If(current_city == Amsterdam, exit_[i] == entry[i] + 1,
               z3.If(current_city == Mykonos, exit_[i] == entry[i] + 4,
                                               z3.BoolVal(False))))

# Flight connectivity constraints between consecutive cities
for i in range(2):
    s.add(z3.Or([z3.And(c[i] == a, c[i+1] == b) for (a, b) in allowed_flights]))

# Total trip duration must be 7 days
s.add(exit_[2] == 7)

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