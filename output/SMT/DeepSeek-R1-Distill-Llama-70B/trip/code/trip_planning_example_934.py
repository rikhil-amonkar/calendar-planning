from z3 import *

# Define cities and their required days
cities = {
    0: 'Brussels',
    1: 'Valencia',
    2: 'Rome',
    3: 'Dubrovnik',
    4: 'Geneva',
    5: 'Budapest',
    6: 'Riga'
}

required_days = {
    0: 5,
    1: 2,
    2: 2,
    3: 3,
    4: 5,
    5: 2,
    6: 4
}

# Define allowed transitions between cities
allowed_transitions = [
    (0, 1),  # Brussels → Valencia
    (2, 1),  # Rome → Valencia
    (0, 4),  # Brussels → Geneva
    (2, 4),  # Rome → Geneva
    (3, 4),  # Dubrovnik → Geneva
    (1, 4),  # Valencia → Geneva
    (2, 6),  # Rome → Riga
    (4, 5),  # Geneva → Budapest
    (6, 0),  # Riga → Brussels
    (2, 5),  # Rome → Budapest
    (2, 0),  # Rome → Brussels
    (0, 5),  # Brussels → Budapest
    (3, 2)   # Dubrovnik → Rome
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(17)]

solver = Solver()

# Add domain constraints for each day
for i in range(17):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 6)

# Add specific day constraints
# Workshop in Brussels between day 7 and day 11
for i in range(6, 11):
    solver.add(days[i] == 0)
# Meet friends in Riga between day 4 and day 7
for i in range(3, 7):
    solver.add(days[i] == 6)
# Meet a friend in Budapest between day 16 and day 17
solver.add(days[15] == 5)
solver.add(days[16] == 5)

# Add transition constraints
for i in range(16):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(17)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(17):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")