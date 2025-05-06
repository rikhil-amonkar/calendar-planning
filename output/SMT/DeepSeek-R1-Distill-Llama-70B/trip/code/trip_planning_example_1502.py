from z3 import *

# Define cities and their required days
cities = {
    0: 'Santorini',
    1: 'Valencia',
    2: 'Madrid',
    3: 'Seville',
    4: 'Bucharest',
    5: 'Vienna',
    6: 'Riga',
    7: 'Tallinn',
    8: 'Krakow',
    9: 'Frankfurt'
}

required_days = {
    0: 3,
    1: 4,
    2: 2,
    3: 2,
    4: 3,
    5: 4,
    6: 4,
    7: 5,
    8: 5,
    9: 4
}

# Define allowed transitions between cities
allowed_transitions = [
    (5, 4), (0, 2), (3, 1), (5, 3), (2, 1), (4, 6), (1, 4), (0, 4),
    (5, 1), (5, 2), (1, 8), (1, 9), (8, 9), (6, 7), (5, 8), (5, 9),
    (2, 3), (0, 5), (5, 6), (9, 7), (9, 4), (2, 4), (2, 9), (9, 6),
    (9, 5)
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
# Vienna between day 3 and day 6
for i in range(2, 6):
    solver.add(days[i] == 5)
# Madrid between day 6 and day 7
solver.add(days[5] == 2)
solver.add(days[6] == 2)
# Riga between day 20 and day 23
for i in range(19, 23):
    solver.add(days[i] == 6)
# Tallinn between day 23 and day 27
for i in range(22, 27):
    solver.add(days[i] == 7)
# Krakow between day 11 and day 15
for i in range(10, 15):
    solver.add(days[i] == 8)

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