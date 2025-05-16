import z3

# Define cities and their required days
cities = ['Madrid', 'Seville', 'Porto', 'Stuttgart']
required_days = [4, 2, 3, 7]

# Assign each city a unique ID
Madrid, Seville, Porto, Stuttgart = 0, 1, 2, 3

# Define direct flights (both directions)
flights = [
    (Porto, Stuttgart),
    (Seville, Porto),
    (Madrid, Porto),
    (Madrid, Seville)
]

# Initialize solver
s = z3.Solver()

# Sequence of cities (c0 to c3)
c = [z3.Int(f'c{i}') for i in range(4)]

# Entry and exit days variables
entry = [z3.Int(f'entry{i}') for i in range(4)]
exit_ = [z3.Int(f'exit{i}') for i in range(4)]

# Madrid must be first city, Stuttgart last
s.add(c[0] == Madrid)
s.add(c[3] == Stuttgart)

# All cities visited exactly once
s.add(z3.Distinct(c))

# Flight constraints (all consecutive cities must have direct connection)
allowed_flights = {(a, b) for a, b in flights} | {(b, a) for a, b in flights}
for i in range(3):
    current = c[i]
    next_city = c[i+1]
    s.add(z3.Or([z3.And(current == a, next_city == b) for (a, b) in allowed_flights]))

# Temporal constraints
s.add(entry[0] == 1)  # Start in Madrid on day 1
s.add(exit_[0] == entry[0] + required_days[Madrid] - 1)  # Madrid stay: 4 days (1-4)

# Subsequent cities' entry/exit days
for i in range(1, 4):
    s.add(entry[i] == exit_[i-1])  # Start next city immediately after previous
    # Get required days for current city
    req_days = z3.If(c[i] == Madrid, required_days[Madrid],
                    z3.If(c[i] == Seville, required_days[Seville],
                        z3.If(c[i] == Porto, required_days[Porto],
                            required_days[Stuttgart])))
    s.add(exit_[i] == entry[i] + req_days - 1)

# Stuttgart must cover days 7-13 (conference)
s.add(entry[3] == 7)
s.add(exit_[3] == 13)

# Madrid must be visited between days 1-4 (relatives visit)
s.add(exit_[0] <= 4)

# Solve and print results
if s.check() == z3.sat:
    m = s.model()
    order = [m.eval(city).as_long() for city in c]
    entry_days = [m.eval(e).as_long() for e in entry]
    exit_days = [m.eval(e).as_long() for e in exit_]
    
    print("Valid trip plan:")
    for i in range(4):
        print(f"{cities[order[i]]}: Day {entry_days[i]} to {exit_days[i]}")
else:
    print("No valid trip plan found")