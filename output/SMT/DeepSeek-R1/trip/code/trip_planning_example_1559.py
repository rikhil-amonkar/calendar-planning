import z3

# Define cities and their required days
cities = ['Valencia', 'Oslo', 'Lyon', 'Prague', 'Paris', 'Nice', 'Seville', 'Tallinn', 'Mykonos', 'Lisbon']
required_days = [2, 3, 4, 3, 4, 4, 5, 2, 5, 2]

# Assign each city a unique ID
Valencia, Oslo, Lyon, Prague, Paris, Nice, Seville, Tallinn, Mykonos, Lisbon = range(10)

# Define direct flights as tuples of city IDs
flights = [
    (Lisbon, Paris),
    (Lyon, Nice),
    (Tallinn, Oslo),
    (Prague, Lyon),
    (Paris, Oslo),
    (Lisbon, Seville),
    (Prague, Lisbon),
    (Oslo, Nice),
    (Valencia, Paris),
    (Valencia, Lisbon),
    (Paris, Nice),
    (Nice, Mykonos),
    (Paris, Lyon),
    (Valencia, Lyon),
    (Prague, Oslo),
    (Prague, Paris),
    (Seville, Paris),
    (Oslo, Lyon),
    (Prague, Valencia),
    (Lisbon, Nice),
    (Lisbon, Oslo),
    (Valencia, Seville),
    (Lisbon, Lyon),
    (Paris, Tallinn),
    (Prague, Tallinn)
]

# Initialize the solver
s = z3.Solver()

# Variables for the sequence of cities (c0 to c9)
c = [z3.Int(f'c{i}') for i in range(10)]

# Variables for entry and exit days of each city in the sequence
entry = [z3.Int(f'entry{i}') for i in range(10)]
exit_ = [z3.Int(f'exit{i}') for i in range(10)]

# All cities must be visited exactly once
s.add(z3.Distinct(c))

# Mykonos must be the last city with entry=21 and exit=25
s.add(c[9] == Mykonos)
s.add(entry[9] == 21)
s.add(exit_[9] == 25)

# Valencia must have entry=3 and exit=4
for i in range(10):
    s.add(z3.Implies(c[i] == Valencia, entry[i] == 3))
    s.add(z3.Implies(c[i] == Valencia, exit_[i] == 4))

# Seville must have entry=5 and exit=9
for i in range(10):
    s.add(z3.Implies(c[i] == Seville, entry[i] == 5))
    s.add(z3.Implies(c[i] == Seville, exit_[i] == 9))

# Oslo must be visited between days 11 and 15
for i in range(10):
    s.add(z3.Implies(c[i] == Oslo, z3.And(entry[i] >= 11, entry[i] <= 15)))

# Entry and exit day constraints
s.add(entry[0] == 1)
for i in range(10):
    req_day = z3.If(
        c[i] == Valencia, 2,
        z3.If(c[i] == Oslo, 3,
        z3.If(c[i] == Lyon, 4,
        z3.If(c[i] == Prague, 3,
        z3.If(c[i] == Paris, 4,
        z3.If(c[i] == Nice, 4,
        z3.If(c[i] == Seville, 5,
        z3.If(c[i] == Tallinn, 2,
        z3.If(c[i] == Mykonos, 5,
        z3.If(c[i] == Lisbon, 2, 0)))))))))
    s.add(exit_[i] == entry[i] + req_day - 1)
    if i < 9:
        s.add(entry[i + 1] == exit_[i])

# Consecutive cities must have a direct flight
for i in range(9):
    allowed_flights = []
    for (a, b) in flights:
        allowed_flights.append(z3.And(c[i] == a, c[i + 1] == b))
        allowed_flights.append(z3.And(c[i] == b, c[i + 1] == a))
    s.add(z3.Or(allowed_flights))

# Check for a solution and output the plan
if s.check() == z3.sat:
    m = s.model()
    order = [m.eval(c[i]).as_long() for i in range(10)]
    entry_days = [m.eval(entry[i]).as_long() for i in range(10)]
    exit_days = [m.eval(exit_[i]).as_long() for i in range(10)]
    
    print("Trip Plan:")
    for i in range(10):
        city = cities[order[i]]
        print(f"From day {entry_days[i]} to day {exit_days[i]}: {city}")
else:
    print("No valid trip plan found.")