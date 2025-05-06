from z3 import *

# Define cities and their required days
cities = {
    0: 'Amsterdam',
    1: 'Edinburgh',
    2: 'Brussels',
    3: 'Vienna',
    4: 'Berlin',
    5: 'Reykjavik'
}

required_days = {
    0: 4,
    1: 5,
    2: 5,
    3: 5,
    4: 4,
    5: 5
}

# Define allowed transitions between cities
allowed_transitions = [
    (1, 4), (0, 4), (1, 0), (3, 4), (4, 2), (3, 5), (1, 2), (3, 2),
    (0, 5), (5, 2), (0, 3), (5, 4)
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(23)]

solver = Solver()

# Add domain constraints for each day
for i in range(23):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 5)

# Add specific day constraints
# Amsterdam between day 5 and day 8
solver.add(Or([days[i] == 0 for i in range(4, 8)]))
# Reykjavik between day 12 and day 16
solver.add(Or([days[i] == 5 for i in range(11, 16)]))
# Berlin between day 16 and day 19
solver.add(Or([days[i] == 4 for i in range(15, 19)]))

# Add transition constraints
for i in range(22):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(23)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(23):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")