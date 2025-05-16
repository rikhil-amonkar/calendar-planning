import z3

# Define cities and their required days
cities = ['Riga', 'Manchester', 'Bucharest', 'Florence', 'Vienna', 'Istanbul', 'Reykjavik', 'Stuttgart']
required_days = [4, 5, 4, 4, 2, 2, 4, 5]

# Assign city IDs
Riga, Manchester, Bucharest, Florence, Vienna, Istanbul, Reykjavik, Stuttgart = range(8)

# Define allowed flights (directed)
allowed_flights = [
    (Bucharest, Vienna), (Vienna, Bucharest),
    (Reykjavik, Vienna), (Vienna, Reykjavik),
    (Manchester, Vienna), (Vienna, Manchester),
    (Manchester, Riga), (Riga, Manchester),
    (Riga, Vienna), (Vienna, Riga),
    (Istanbul, Vienna), (Vienna, Istanbul),
    (Vienna, Florence), (Florence, Vienna),
    (Stuttgart, Vienna), (Vienna, Stuttgart),
    (Riga, Bucharest), (Bucharest, Riga),
    (Istanbul, Riga), (Riga, Istanbul),
    (Stuttgart, Istanbul), (Istanbul, Stuttgart),
    (Reykjavik, Stuttgart),  # One-way flight
    (Istanbul, Bucharest), (Bucharest, Istanbul),
    (Manchester, Istanbul), (Istanbul, Manchester),
    (Manchester, Bucharest), (Bucharest, Manchester),
    (Stuttgart, Manchester), (Manchester, Stuttgart),
]

# Initialize solver
s = z3.Solver()

# Sequence variables for 8 cities
c = [z3.Int(f'c{i}') for i in range(8)]
entry = [z3.Int(f'entry{i}') for i in range(8)]
exit_ = [z3.Int(f'exit{i}') for i in range(8)]

# Each city visited exactly once
s.add(z3.Distinct(c))

# Entry and exit constraints for each city
for i in range(8):
    current = c[i]
    # Bucharest must be days 16-19
    s.add(z3.Implies(current == Bucharest, z3.And(entry[i] == 16, exit_[i] == 19))
    # Istanbul must be days 12-13
    s.add(z3.Implies(current == Istanbul, z3.And(entry[i] == 12, exit_[i] == 13))
    # Other cities' duration constraints
    for city in [Riga, Manchester, Florence, Vienna, Reykjavik, Stuttgart]:
        s.add(z3.Implies(current == city, exit_[i] == entry[i] + required_days[city] - 1))

# Consecutive entry days alignment
for i in range(7):
    s.add(entry[i+1] == exit_[i])

# Flight connectivity between consecutive cities
for i in range(7):
    current = c[i]
    next_c = c[i+1]
    s.add(z3.Or([z3.And(current == a, next_c == b) for (a, b) in allowed_flights]))

# Start on day 1 and end on day 23
s.add(entry[0] == 1)
s.add(exit_[7] == 23)

# Solve and output
if s.check() == z3.sat:
    m = s.model()
    order = [m.eval(c[i]).as_long() for i in range(8)]
    entry_days = [m.eval(entry[i]).as_long() for i in range(8)]
    exit_days = [m.eval(exit_[i]).as_long() for i in range(8)]
    
    print("Valid trip plan:")
    for i in range(8):
        print(f"{cities[order[i]]}: Day {entry_days[i]} to {exit_days[i]}")
else:
    print("No valid trip plan found")