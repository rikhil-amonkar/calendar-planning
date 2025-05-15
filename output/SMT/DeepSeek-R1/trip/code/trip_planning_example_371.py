import z3

# Define cities and their required days
cities = ['Vienna', 'Nice', 'Stockholm', 'Split']
required_days = [2, 2, 5, 3]

# Assign city IDs
Vienna, Nice, Stockholm, Split = 0, 1, 2, 3

# Define allowed flights (bidirectional pairs)
allowed_flights = [
    (Vienna, Stockholm), (Stockholm, Vienna),
    (Vienna, Nice), (Nice, Vienna),
    (Vienna, Split), (Split, Vienna),
    (Stockholm, Split), (Split, Stockholm),
    (Nice, Stockholm), (Stockholm, Nice)
]

# Initialize solver
s = z3.Solver()

# Sequence of cities (c0 to c3)
c = [z3.Int(f'c{i}') for i in range(4)]
entry = [z3.Int(f'entry{i}') for i in range(4)]
exit_ = [z3.Int(f'exit{i}') for i in range(4)]

# All cities visited exactly once
s.add(z3.Distinct(c))

# Fixed constraints for Vienna (first city) and Split (last city)
s.add(c[0] == Vienna)
s.add(entry[0] == 1)
s.add(exit_[0] == 2)  # 1 + 2 -1 = 2

s.add(c[3] == Split)
s.add(entry[3] == 7)
s.add(exit_[3] == 9)  # 7 +3 -1 =9

# Entry-exit relationships and required days
for i in range(4):
    current = c[i]
    req = z3.If(current == Vienna, 2,
            z3.If(current == Nice, 2,
                z3.If(current == Stockholm, 5, 3)))
    s.add(exit_[i] == entry[i] + req - 1)

# Consecutive city entry days must align
for i in range(3):
    s.add(entry[i+1] == exit_[i])

# Flight connectivity constraints between consecutive cities
for i in range(3):
    current = c[i]
    next_c = c[i+1]
    s.add(z3.Or([z3.And(current == a, next_c == b) for (a, b) in allowed_flights]))

# Solve and output
if s.check() == z3.sat:
    m = s.model()
    order = [m.eval(c[i]).as_long() for i in range(4)]
    entry_days = [m.eval(entry[i]).as_long() for i in range(4)]
    exit_days = [m.eval(exit_[i]).as_long() for i in range(4)]
    
    print("Valid trip plan:")
    for i in range(4):
        print(f"{cities[order[i]]}: Day {entry_days[i]} to {exit_days[i]}")
else:
    print("No valid trip plan found")