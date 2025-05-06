from z3 import *

# Define cities and their required days
cities = {
    0: 'Valencia',
    1: 'Oslo',
    2: 'Lyon',
    3: 'Prague',
    4: 'Paris',
    5: 'Nice',
    6: 'Seville',
    7: 'Tallinn',
    8: 'Mykonos',
    9: 'Lisbon'
}

required_days = {
    0: 2,
    1: 3,
    2: 4,
    3: 3,
    4: 4,
    5: 4,
    6: 5,
    7: 2,
    8: 5,
    9: 2
}

# Define allowed transitions between cities
allowed_transitions = [
    (9, 4),  # Lisbon → Paris
    (2, 5),  # Lyon → Nice
    (7, 1),  # Tallinn → Oslo
    (3, 2),  # Prague → Lyon
    (4, 1),  # Paris → Oslo
    (9, 6),  # Lisbon → Seville
    (3, 9),  # Prague → Lisbon
    (1, 5),  # Oslo → Nice
    (0, 4),  # Valencia → Paris
    (0, 9),  # Valencia → Lisbon
    (4, 5),  # Paris → Nice
    (5, 8),  # Nice → Mykonos
    (4, 2),  # Paris → Lyon
    (0, 2),  # Valencia → Lyon
    (3, 1),  # Prague → Oslo
    (3, 4),  # Prague → Paris
    (6, 4),  # Seville → Paris
    (1, 2),  # Oslo → Lyon
    (3, 0),  # Prague → Valencia
    (9, 5),  # Lisbon → Nice
    (9, 1),  # Lisbon → Oslo
    (0, 6),  # Valencia → Seville
    (9, 2),  # Lisbon → Lyon
    (4, 7),  # Paris → Tallinn
    (3, 7)   # Prague → Tallinn
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(25)]

solver = Solver()

# Add domain constraints for each day
for i in range(25):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 9)

# Add specific day constraints
# Meet friends in Valencia between day 3 and day 4
solver.add(days[2] == 0)
solver.add(days[3] == 0)
# Annual show in Seville between day 5 and day 9
for i in range(4, 9):
    solver.add(days[i] == 6)
# Meet a friend in Oslo between day 13 and day 15
for i in range(12, 15):
    solver.add(days[i] == 1)
# Attend wedding in Mykonos between day 21 and day 25
for i in range(20, 25):
    solver.add(days[i] == 8)

# Add transition constraints
for i in range(24):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(25)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(25):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")