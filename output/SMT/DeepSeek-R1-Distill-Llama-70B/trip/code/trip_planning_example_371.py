from z3 import *

# Define cities and their required days
cities = {
    0: 'Nice',
    1: 'Stockholm',
    2: 'Split',
    3: 'Vienna'
}

required_days = {
    0: 2,
    1: 5,
    2: 3,
    3: 2
}

# Define allowed transitions between cities
allowed_transitions = [
    (3, 1),  # Vienna → Stockholm
    (3, 0),  # Vienna → Nice
    (3, 2),  # Vienna → Split
    (1, 2),  # Stockholm → Split
    (0, 1)   # Nice → Stockholm
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(9)]

solver = Solver()

# Add domain constraints for each day
for i in range(9):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 3)

# Add specific day constraints
# Workshop in Vienna on day 1 and day 2
solver.add(days[0] == 3)
solver.add(days[1] == 3)
# Conference in Split on day 7 and day 9
solver.add(days[6] == 2)
solver.add(days[8] == 2)

# Add transition constraints
for i in range(8):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(9)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(9):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")