import z3

# Define cities and their required days
cities = ['Geneva', 'Paris', 'Porto', 'Reykjavik', 'Oslo']
required_days = [7, 6, 7, 2, 5]
Geneva, Paris, Porto, Reykjavik, Oslo = 0, 1, 2, 3, 4

# Define allowed flights (both directions where applicable)
allowed_flights = [
    (Paris, Oslo), (Oslo, Paris),
    (Geneva, Oslo), (Oslo, Geneva),
    (Porto, Paris), (Paris, Porto),
    (Geneva, Paris), (Paris, Geneva),
    (Geneva, Porto), (Porto, Geneva),
    (Paris, Reykjavik), (Reykjavik, Paris),
    (Reykjavik, Oslo), (Oslo, Reykjavik),
    (Porto, Oslo), (Oslo, Porto)
]

# Initialize solver
s = z3.Solver()

# Sequence variables for 5 cities
c = [z3.Int(f'c{i}') for i in range(5)]
entry = [z3.Int(f'entry{i}') for i in range(5)]
exit_ = [z3.Int(f'exit{i}') for i in range(5)]

# Each city visited exactly once
s.add(z3.Distinct(c))

# Fixed start and end cities with specific dates
s.add(c[0] == Geneva)
s.add(entry[0] == 1)
s.add(exit_[0] == 7)  # Geneva: days 1-7

s.add(c[4] == Oslo)
s.add(entry[4] == 19)
s.add(exit_[4] == 23)  # Oslo: days 19-23

# Entry/exit constraints for middle cities
for i in range(1, 4):
    s.add(entry[i] == exit_[i-1])  # Consecutive entry days
    city = c[i]
    s.add(exit_[i] == entry[i] + (required_days[city] - 1))

# Flight connectivity between consecutive cities
for i in range(4):
    s.add(z3.Or([z3.And(c[i] == a, c[i+1] == b) for (a, b) in allowed_flights]))

# Total trip duration constraint (enforced by Oslo's exit day)
s.add(exit_[4] == 23)

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