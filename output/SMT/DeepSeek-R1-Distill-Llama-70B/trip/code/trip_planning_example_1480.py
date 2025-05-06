from z3 import *

# Define cities and their required days
cities = {
    0: 'Istanbul',
    1: 'Vienna',
    2: 'Riga',
    3: 'Brussels',
    4: 'Madrid',
    5: 'Vilnius',
    6: 'Venice',
    7: 'Geneva',
    8: 'Munich',
    9: 'Reykjavik'
}

required_days = {
    0: 4,
    1: 4,
    2: 2,
    3: 2,
    4: 4,
    5: 4,
    6: 5,
    7: 4,
    8: 5,
    9: 2
}

# Define allowed transitions between cities
allowed_transitions = [
    (8, 1), (0, 3), (1, 5), (4, 8), (6, 3), (2, 3), (7, 0),
    (8, 9), (1, 0), (2, 0), (9, 1), (6, 8), (4, 6), (5, 0),
    (6, 0), (6, 1), (9, 4), (2, 8), (8, 0), (9, 3), (5, 3),
    (8, 5), (1, 2), (1, 3), (7, 1), (4, 3), (4, 8), (7, 8),
    (4, 0), (7, 4), (8, 3), (4, 9), (2, 5), (3, 5), (8, 5),
    (1, 3), (1, 2), (7, 3), (7, 4), (8, 3), (4, 1), (9, 4)
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
# Visit relatives in Geneva between day 1 and day 4
for i in range(4):
    solver.add(days[i] == 7)
# Attend workshop in Venice between day 7 and day 11
for i in range(6, 11):
    solver.add(days[i] == 6)
# Meet friends in Vilnius between day 20 and day 23
for i in range(19, 23):
    solver.add(days[i] == 5)
# Attend wedding in Brussels between day 26 and day 27
solver.add(days[25] == 3)
solver.add(days[26] == 3)

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