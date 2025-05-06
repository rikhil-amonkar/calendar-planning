from z3 import *

# Define cities and their required days
cities = {
    0: 'Lyon',
    1: 'Paris',
    2: 'Riga',
    3: 'Berlin',
    4: 'Stockholm',
    5: 'Zurich',
    6: 'Nice',
    7: 'Seville',
    8: 'Milan',
    9: 'Naples'
}

required_days = {
    0: 3,
    1: 5,
    2: 2,
    3: 2,
    4: 3,
    5: 5,
    6: 2,
    7: 3,
    8: 3,
    9: 4
}

# Define allowed transitions between cities
allowed_transitions = [
    (1, 4), (7, 1), (9, 5), (6, 2), (3, 8), (1, 5), (1, 6), (8, 1),
    (8, 2), (1, 0), (8, 9), (1, 2), (3, 4), (4, 2), (6, 5), (8, 5),
    (5, 4), (5, 2), (3, 9), (8, 4), (3, 5), (8, 7), (1, 9), (3, 2),
    (6, 4), (3, 1), (6, 9), (3, 6)
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
    solver.add(days[i] <= 9)

# Add specific day constraints
# Berlin between day 1 and day 2
solver.add(days[0] == 3)
solver.add(days[1] == 3)
# Stockholm between day 20 and day 22
solver.add(Or([days[i] == 4 for i in [19, 20, 21]]))
# Nice between day 12 and day 13
solver.add(days[11] == 6)
solver.add(days[12] == 6)

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