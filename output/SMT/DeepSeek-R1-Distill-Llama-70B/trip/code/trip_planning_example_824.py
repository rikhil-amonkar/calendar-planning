from z3 import *

# Define cities and their required days
cities = {
    0: 'Berlin',
    1: 'Split',
    2: 'Bucharest',
    3: 'Riga',
    4: 'Lisbon',
    5: 'Tallinn',
    6: 'Lyon'
}

required_days = {
    0: 5,
    1: 3,
    2: 3,
    3: 5,
    4: 3,
    5: 4,
    6: 5
}

# Define allowed transitions between cities
allowed_transitions = [
    (4, 2),  # Lisbon → Bucharest
    (0, 4),  # Berlin → Lisbon
    (2, 3),  # Bucharest → Riga
    (0, 3),  # Berlin → Riga
    (1, 6),  # Split → Lyon
    (4, 3),  # Lisbon → Riga
    (3, 5),  # Riga → Tallinn
    (0, 1),  # Berlin → Split
    (6, 4),  # Lyon → Lisbon
    (0, 5),  # Berlin → Tallinn
    (6, 2)   # Lyon → Bucharest
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(22)]

solver = Solver()

# Add domain constraints for each day
for i in range(22):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 6)

# Add specific day constraints
# Berlin between day 1 and day 5
for i in range(5):
    solver.add(days[i] == 0)
# Lyon between day 7 and day 11
for i in range(6, 11):
    solver.add(days[i] == 6)
# Bucharest between day 13 and day 15
for i in range(12, 15):
    solver.add(days[i] == 2)

# Add transition constraints
for i in range(21):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(22)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(22):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")