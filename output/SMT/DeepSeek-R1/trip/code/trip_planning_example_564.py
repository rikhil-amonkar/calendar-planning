import z3

# Define cities and their required days
cities = ['Istanbul', 'Rome', 'Seville', 'Naples', 'Santorini']
required_days = [2, 3, 4, 7, 4]

# Assign city IDs
Istanbul, Rome, Seville, Naples, Santorini = 0, 1, 2, 3, 4

# Define allowed flights (bidirectional pairs)
allowed_flights = [
    (Rome, Santorini), (Santorini, Rome),
    (Seville, Rome), (Rome, Seville),
    (Istanbul, Naples), (Naples, Istanbul),
    (Naples, Santorini), (Santorini, Naples),
    (Rome, Naples), (Naples, Rome),
    (Rome, Istanbul), (Istanbul, Rome)
]

# Initialize solver
s = z3.Solver()

# Sequence of cities (c0 to c4)
c = [z3.Int(f'c{i}') for i in range(5)]

# Entry and exit days variables
entry = [z3.Int(f'entry{i}') for i in range(5)]
exit_ = [z3.Int(f'exit{i}') for i in range(5)]

# All cities visited exactly once
s.add(z3.Distinct(c))

# Santorini must be last (wedding constraint)
s.add(c[4] == Santorini)
s.add(entry[4] == 13)
s.add(exit_[4] == 16)

# Istanbul must be visited between day 6-7
for i in range(5):
    s.add(z3.Implies(c[i] == Istanbul, entry[i] == 6))
    s.add(z3.Implies(c[i] == Istanbul, exit_[i] == 7))

# First city starts on day 1
s.add(entry[0] == 1)

# Entry-exit relationships and required days
for i in range(5):
    current = c[i]
    req = z3.If(
        current == Istanbul, 2,
        z3.If(current == Rome, 3,
            z3.If(current == Seville, 4,
                z3.If(current == Naples, 7, 4)))
    )
    s.add(exit_[i] == entry[i] + req - 1)

# Consecutive city entry days must align
for i in range(4):
    s.add(entry[i+1] == exit_[i])

# Flight connectivity constraints
for i in range(4):
    current = c[i]
    next_c = c[i+1]
    s.add(z3.Or([z3.And(current == a, next_c == b) for (a, b) in allowed_flights]))

# Solve and output
if s.check() == z3.sat:
    m = s.model()
    order = [m.eval(c[i]).as_long() for i in range(5)]
    entry_days = [m.eval(entry[i]).as_long() for i in range(5)]
    exit_days = [m.eval(exit_[i]).as_long() for i in range(5)]
    
    print("Valid trip plan:")
    for i in range(5):
        print(f"{cities[order[i]]}: Day {entry_days[i]} to {exit_days[i]}")
else:
    print("No valid trip plan found")