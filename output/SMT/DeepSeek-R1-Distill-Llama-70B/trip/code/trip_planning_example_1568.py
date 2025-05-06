from z3 import *

# Define cities and their required days
cities = {
    0: 'Prague',
    1: 'Brussels',
    2: 'Riga',
    3: 'Munich',
    4: 'Seville',
    5: 'Stockholm',
    6: 'Istanbul',
    7: 'Amsterdam',
    8: 'Vienna',
    9: 'Split'
}

required_days = {
    0: 5,
    1: 2,
    2: 2,
    3: 2,
    4: 3,
    5: 2,
    6: 2,
    7: 3,
    8: 5,
    9: 3
}

# Define allowed transitions between cities
allowed_transitions = [
    (2, 5), (5, 1), (6, 3), (6, 2), (0, 9), (8, 1), (8, 2), (9, 5),
    (3, 7), (9, 7), (7, 5), (7, 2), (8, 5), (8, 6), (8, 4), (6, 7),
    (3, 1), (0, 3), (2, 3), (0, 1), (0, 6), (6, 5), (8, 0), (3, 9),
    (8, 7), (0, 5), (1, 4), (3, 5), (6, 1), (7, 4), (8, 9), (3, 4),
    (2, 1), (0, 2), (8, 3)
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(20)]

solver = Solver()

# Add domain constraints for each day
for i in range(20):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 9)

# Add specific day constraints
# Vienna between day 1 and day 5
for i in range(5):
    solver.add(days[i] == 8)
# Prague between day 5 and day 9
for i in range(5, 10):
    solver.add(days[i] == 0)
# Riga between day 15 and day 16
solver.add(days[14] == 2)
solver.add(days[15] == 2)
# Stockholm between day 16 and day 17
solver.add(days[15] == 5)
solver.add(days[16] == 5)
# Split between day 11 and day 13
for i in range(10, 14):
    solver.add(days[i] == 9)

# Add transition constraints
for i in range(19):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(20)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(20):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")