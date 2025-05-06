from z3 import *

# Define cities and their required days
cities = {
    0: 'Santorini',
    1: 'Krakow',
    2: 'Paris',
    3: 'Vilnius',
    4: 'Munich',
    5: 'Geneva',
    6: 'Amsterdam',
    7: 'Budapest',
    8: 'Split'
}

required_days = {
    0: 5,
    1: 5,
    2: 5,
    3: 3,
    4: 5,
    5: 2,
    6: 4,
    7: 5,
    8: 4
}

# Define allowed transitions between cities
allowed_transitions = [
    (2, 1), (2, 6), (2, 8), (3, 4), (2, 5), (6, 5), (4, 8), (8, 1),
    (4, 6), (7, 6), (8, 5), (3, 8), (4, 5), (4, 1), (1, 3), (3, 6),
    (3, 2), (7, 2), (7, 5), (8, 6), (0, 5), (6, 0), (4, 7), (4, 2)
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(30)]

solver = Solver()

# Add domain constraints for each day
for i in range(30):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 8)

# Add specific day constraints
# Paris between day 11 and day 15
solver.add(Or([days[i] == 2 for i in range(10, 15)]))
# Krakow between day 18 and day 22
solver.add(Or([days[i] == 1 for i in range(17, 22)]))
# Santorini between day 25 and day 29
solver.add(Or([days[i] == 0 for i in range(24, 29)]))

# Add transition constraints
for i in range(29):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(30)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(30):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")