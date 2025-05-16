import z3

# Define cities and their required days
cities = ['Brussels', 'Rome', 'Dubrovnik', 'Geneva', 'Budapest', 'Riga', 'Valencia']
required_days = [5, 2, 3, 5, 2, 4, 2]

# Assign city IDs
Brussels, Rome, Dubrovnik, Geneva, Budapest, Riga, Valencia = range(7)

# Define allowed flights (directed)
allowed_flights = [
    (Brussels, Valencia), (Valencia, Brussels),
    (Rome, Valencia), (Valencia, Rome),
    (Brussels, Geneva), (Geneva, Brussels),
    (Rome, Geneva), (Geneva, Rome),
    (Dubrovnik, Geneva), (Geneva, Dubrovnik),
    (Valencia, Geneva), (Geneva, Valencia),
    (Rome, Riga),  # One-way flight
    (Geneva, Budapest), (Budapest, Geneva),
    (Riga, Brussels), (Brussels, Riga),
    (Rome, Budapest), (Budapest, Rome),
    (Rome, Brussels), (Brussels, Rome),
    (Brussels, Budapest), (Budapest, Brussels),
    (Dubrovnik, Rome), (Rome, Dubrovnik)
]

# Initialize solver
s = z3.Solver()

# Sequence variables for 7 cities
c = [z3.Int(f'c{i}') for i in range(7)]
entry = [z3.Int(f'entry{i}') for i in range(7)]
exit_ = [z3.Int(f'exit{i}') for i in range(7)]

# Each city visited exactly once
s.add(z3.Distinct(c))

# Entry and exit constraints for each city
for i in range(7):
    current = c[i]
    s.add(z3.Or(
        z3.And(current == Brussels, entry[i] == 7, exit_[i] == 11),
        z3.And(current == Budapest, entry[i] == 16, exit_[i] == 17),
        z3.And(current == Riga, entry[i] == 4, exit_[i] == 7),
        z3.And(current == Rome, exit_[i] == entry[i] + 1),
        z3.And(current == Dubrovnik, exit_[i] == entry[i] + 2),
        z3.And(current == Geneva, exit_[i] == entry[i] + 4),
        z3.And(current == Valencia, exit_[i] == entry[i] + 1)
    ))

# Consecutive entry days alignment
for i in range(6):
    s.add(entry[i+1] == exit_[i])

# Flight connectivity between consecutive cities
for i in range(6):
    current = c[i]
    next_c = c[i+1]
    s.add(z3.Or([z3.And(current == a, next_c == b) for (a, b) in allowed_flights]))

# Start on day 1 and end on day 17
s.add(entry[0] == 1)
s.add(exit_[6] == 17)

# Solve and output
if s.check() == z3.sat:
    m = s.model()
    order = [m.eval(c[i]).as_long() for i in range(7)]
    entry_days = [m.eval(entry[i]).as_long() for i in range(7)]
    exit_days = [m.eval(exit_[i]).as_long() for i in range(7)]
    
    print("Valid trip plan:")
    for i in range(7):
        print(f"{cities[order[i]]}: Day {entry_days[i]} to {exit_days[i]}")
else:
    print("No valid trip plan found")