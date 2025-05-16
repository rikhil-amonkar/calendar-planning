import z3

# Define cities and their required days
cities = ['Istanbul', 'Vienna', 'Riga', 'Brussels', 'Madrid', 'Vilnius', 'Venice', 'Geneva', 'Munich', 'Reykjavik']
required_days = [4, 4, 2, 2, 4, 4, 5, 4, 5, 2]

# Assign city IDs
(Istanbul, Vienna, Riga, Brussels, Madrid, 
 Vilnius, Venice, Geneva, Munich, Reykjavik) = range(10)

# Define allowed flights (including one-way where specified)
allowed_flights = [
    (Munich, Vienna), (Vienna, Munich),
    (Istanbul, Brussels), (Brussels, Istanbul),
    (Vienna, Vilnius), (Vilnius, Vienna),
    (Madrid, Munich), (Munich, Madrid),
    (Venice, Brussels), (Brussels, Venice),
    (Riga, Brussels), (Brussels, Riga),
    (Geneva, Istanbul), (Istanbul, Geneva),
    (Munich, Reykjavik), (Reykjavik, Munich),
    (Vienna, Istanbul), (Istanbul, Vienna),
    (Riga, Istanbul), (Istanbul, Riga),
    (Reykjavik, Vienna), (Vienna, Reykjavik),
    (Venice, Munich), (Munich, Venice),
    (Madrid, Venice), (Venice, Madrid),
    (Vilnius, Istanbul), (Istanbul, Vilnius),
    (Venice, Vienna), (Vienna, Venice),
    (Venice, Istanbul), (Istanbul, Venice),
    (Reykjavik, Madrid),
    (Riga, Munich),
    (Munich, Istanbul), (Istanbul, Munich),
    (Reykjavik, Brussels), (Brussels, Reykjavik),
    (Vilnius, Brussels), (Brussels, Vilnius),
    (Vilnius, Munich),
    (Madrid, Vienna), (Vienna, Madrid),
    (Vienna, Riga), (Riga, Vienna),
    (Geneva, Vienna), (Vienna, Geneva),
    (Madrid, Brussels), (Brussels, Madrid),
    (Vienna, Brussels), (Brussels, Vienna),
    (Geneva, Brussels), (Brussels, Geneva),
    (Geneva, Madrid), (Madrid, Geneva),
    (Munich, Brussels), (Brussels, Munich),
    (Madrid, Istanbul), (Istanbul, Madrid),
    (Geneva, Munich), (Munich, Geneva),
    (Riga, Vilnius)
]

# Initialize solver
s = z3.Solver()

# Sequence of cities (c0 to c9)
c = [z3.Int(f'c{i}') for i in range(10)]
entry = [z3.Int(f'entry{i}') for i in range(10)]
exit_ = [z3.Int(f'exit{i}') for i in range(10)]

# All cities visited exactly once
s.add(z3.Distinct(c))

# Fixed constraints for specific cities
s.add(c[0] == Geneva)            # Must start in Geneva
s.add(entry[0] == 1)             # Starts on day 1
s.add(exit_[0] == 4)             # Geneva exit day 4

s.add(c[9] == Brussels)          # Must end in Brussels
s.add(entry[9] == 26)            # Brussels entry day 26
s.add(exit_[9] == 27)            # Brussels exit day 27

# Fixed date constraints for Venice and Vilnius
for i in range(10):
    current = c[i]
    # Venice must be active days 7-11
    s.add(z3.Implies(current == Venice, z3.And(entry[i] == 7, exit_[i] == 11)))
    # Vilnius must be active days 20-23
    s.add(z3.Implies(current == Vilnius, z3.And(entry[i] == 20, exit_[i] == 23)))

# Entry-exit relationships and required days
for i in range(10):
    current = c[i]
    req = z3.If(current == Istanbul, 4,
            z3.If(current == Vienna, 4,
                z3.If(current == Riga, 2,
                    z3.If(current == Brussels, 2,
                        z3.If(current == Madrid, 4,
                            z3.If(current == Vilnius, 4,
                                z3.If(current == Venice, 5,
                                    z3.If(current == Geneva, 4,
                                        z3.If(current == Munich, 5, 2)))))))))
    s.add(exit_[i] == entry[i] + req - 1)

# Consecutive city entry days must align
for i in range(9):
    s.add(entry[i+1] == exit_[i])

# Flight connectivity constraints
for i in range(9):
    current = c[i]
    next_c = c[i+1]
    s.add(z3.Or([z3.And(current == a, next_c == b) for (a, b) in allowed_flights]))

# Solve and output
if s.check() == z3.sat:
    m = s.model()
    order = [m.eval(c[i]).as_long() for i in range(10)]
    entry_days = [m.eval(entry[i]).as_long() for i in range(10)]
    exit_days = [m.eval(exit_[i]).as_long() for i in range(10)]
    
    print("Valid trip plan:")
    for i in range(10):
        print(f"{cities[order[i]]}: Day {entry_days[i]} to {exit_days[i]}")
else:
    print("No valid trip plan found")