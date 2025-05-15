import z3

# Define cities and their required days
cities = ['Riga', 'Frankfurt', 'Amsterdam', 'Vilnius', 'London', 'Stockholm', 'Bucharest']
required_days = [2, 3, 2, 5, 2, 3, 4]

# Assign city IDs
Riga, Frankfurt, Amsterdam, Vilnius, London, Stockholm, Bucharest = 0, 1, 2, 3, 4, 5, 6

# Define allowed flights (including bidirectional where applicable)
allowed_flights = [
    (London, Amsterdam), (Amsterdam, London),
    (Vilnius, Frankfurt), (Frankfurt, Vilnius),
    (Riga, Vilnius),  # One-way from Riga to Vilnius
    (Riga, Stockholm), (Stockholm, Riga),
    (London, Bucharest), (Bucharest, London),
    (Amsterdam, Stockholm), (Stockholm, Amsterdam),
    (Amsterdam, Frankfurt), (Frankfurt, Amsterdam),
    (Frankfurt, Stockholm), (Stockholm, Frankfurt),
    (Bucharest, Riga), (Riga, Bucharest),
    (Amsterdam, Riga), (Riga, Amsterdam),
    (Amsterdam, Bucharest), (Bucharest, Amsterdam),
    (Riga, Frankfurt), (Frankfurt, Riga),
    (Bucharest, Frankfurt), (Frankfurt, Bucharest),
    (London, Frankfurt), (Frankfurt, London),
    (London, Stockholm), (Stockholm, London),
    (Amsterdam, Vilnius), (Vilnius, Amsterdam)
]

# Initialize solver
s = z3.Solver()

# Sequence of cities (c0 to c6)
c = [z3.Int(f'c{i}') for i in range(7)]

# Entry and exit days variables
entry = [z3.Int(f'entry{i}') for i in range(7)]
exit_ = [z3.Int(f'exit{i}') for i in range(7)]

# Each city must be visited exactly once
s.add(z3.Distinct(c))

# Last city must be Stockholm (due to wedding on days 13-15)
s.add(c[6] == Stockholm)

# First city starts on day 1
s.add(entry[0] == 1)

# Entry and exit constraints for each city in the sequence
for i in range(7):
    current_city = c[i]
    # Fixed entry/exit for Amsterdam, Vilnius, Stockholm
    s.add(z3.Implies(current_city == Amsterdam, z3.And(entry[i] == 2, exit_[i] == 3)))
    s.add(z3.Implies(current_city == Vilnius, z3.And(entry[i] == 7, exit_[i] == 11)))
    s.add(z3.Implies(current_city == Stockholm, z3.And(entry[i] == 13, exit_[i] == 15)))
    
    # Calculate exit day based on required days
    req = z3.If(
        current_city == Riga, required_days[Riga],
        z3.If(current_city == Frankfurt, required_days[Frankfurt],
            z3.If(current_city == Amsterdam, required_days[Amsterdam],
                z3.If(current_city == Vilnius, required_days[Vilnius],
                    z3.If(current_city == London, required_days[London],
                        z3.If(current_city == Stockholm, required_days[Stockholm],
                            required_days[Bucharest])))))
    )
    s.add(exit_[i] == entry[i] + req - 1)

# Entry of next city must equal exit of previous
for i in range(1, 7):
    s.add(entry[i] == exit_[i-1])

# Flight constraints between consecutive cities
for i in range(6):
    current = c[i]
    next_c = c[i+1]
    s.add(z3.Or([z3.And(current == a, next_c == b) for (a, b) in allowed_flights]))

# Solve and print results
if s.check() == z3.sat:
    m = s.model()
    order = [m.eval(c[i]).as_long() for i in range(7)]
    entry_days = [m.eval(entry[i]).as_long() for i in range(7)]
    exit_days = [m.eval(exit_[i]).as_long() for i in range(7)]
    
    print("Valid trip plan:")
    for i in range(7):
        city = cities[order[i]]
        print(f"{city}: Day {entry_days[i]} to {exit_days[i]}")
else:
    print("No valid trip plan found")