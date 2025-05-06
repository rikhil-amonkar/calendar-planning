from z3 import *

# Define cities and their required days
cities = {
    0: 'Warsaw',
    1: 'Porto',
    2: 'Naples',
    3: 'Brussels',
    4: 'Split',
    5: 'Reykjavik',
    6: 'Amsterdam',
    7: 'Lyon',
    8: 'Helsinki',
    9: 'Valencia'
}

required_days = {
    0: 3,
    1: 5,
    2: 4,
    3: 3,
    4: 3,
    5: 5,
    6: 4,
    7: 3,
    8: 4,
    9: 2
}

# Define allowed transitions between cities
allowed_transitions = [
    (6, 0), (8, 3), (8, 0), (5, 3), (6, 7), (6, 2), (6, 5), (6, 4), (6, 9),
    (7, 4), (0, 4), (8, 4), (3, 7), (1, 7), (5, 0), (3, 9), (9, 7),
    (1, 0), (0, 9), (0, 3), (0, 2), (2, 9), (2, 4), (8, 2), (8, 5),
    (6, 8), (1, 9), (0, 3), (6, 2)
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(27)]

solver = Solver()

# Add domain constraints for each day
for i in range(27):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 9)

# Add specific day constraints
# Porto between day 1 and day 5
for i in range(5):
    solver.add(Or(days[i] == 1))
solver.add(days[0] == 1)  # At least one day in Porto during days 1-5

# Naples on days 17 and 20
solver.add(days[16] == 2)
solver.add(days[19] == 2)

# Brussels between day 20 and day 22
solver.add(Or([days[i] == 3 for i in [19, 20, 21]]))
solver.add(Or(days[19] == 3, days[20] == 3, days[21] == 3))

# Amsterdam between day 5 and day 8
for i in range(4, 8):
    solver.add(Or(days[i] == 6))
solver.add(Or(days[4] == 6, days[5] == 6, days[6] == 6, days[7] == 6))

# Helsinki between day 8 and day 11
for i in range(8, 12):
    solver.add(Or(days[i] == 8))
solver.add(Or(days[8] == 8, days[9] == 8, days[10] == 8, days[11] == 8))

# Add transition constraints
for i in range(26):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(27)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(27):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")