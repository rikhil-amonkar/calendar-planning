from z3 import *

# Define cities and their required days
cities = {
    0: 'Helsinki',
    1: 'Warsaw',
    2: 'Madrid',
    3: 'Split',
    4: 'Reykjavik',
    5: 'Budapest'
}

required_days = {
    0: 2,
    1: 3,
    2: 4,
    3: 4,
    4: 2,
    5: 4
}

# Define allowed transitions between cities
allowed_transitions = [
    (0, 4),  # Helsinki → Reykjavik
    (5, 1),  # Budapest → Warsaw
    (2, 3),  # Madrid → Split
    (0, 3),  # Helsinki → Split
    (0, 2),  # Helsinki → Madrid
    (0, 5),  # Helsinki → Budapest
    (4, 1),  # Reykjavik → Warsaw
    (0, 1),  # Helsinki → Warsaw
    (2, 5),  # Madrid → Budapest
    (5, 4),  # Budapest → Reykjavik
    (2, 1),  # Madrid → Warsaw
    (1, 3),  # Warsaw → Split
    (4, 2)   # Reykjavik → Madrid
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(14)]

solver = Solver()

# Add domain constraints for each day
for i in range(14):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 5)

# Add specific day constraints
# Attend workshop in Helsinki on day 1 and day 2
solver.add(days[0] == 0)
solver.add(days[1] == 0)
# Visit relatives in Warsaw between day 9 and day 11
solver.add(days[8] == 1)
solver.add(days[9] == 1)
solver.add(days[10] == 1)
# Meet a friend in Reykjavik between day 8 and day 9
solver.add(days[7] == 4)
solver.add(days[8] == 4)

# Add transition constraints
for i in range(13):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(14)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(14):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")