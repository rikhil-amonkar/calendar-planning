from z3 import *

# Define cities and their required days
cities = {
    0: 'Oslo',
    1: 'Stuttgart',
    2: 'Reykjavik',
    3: 'Split',
    4: 'Geneva',
    5: 'Porto',
    6: 'Tallinn',
    7: 'Stockholm'
}

required_days = {
    0: 5,
    1: 5,
    2: 2,
    3: 3,
    4: 2,
    5: 3,
    6: 5,
    7: 3
}

# Define allowed transitions between cities
allowed_transitions = [
    (2, 1),  # Reykjavik → Stuttgart
    (2, 7),  # Reykjavik → Stockholm
    (2, 6),  # Reykjavik → Tallinn
    (2, 0),  # Reykjavik → Oslo
    (1, 5),  # Stuttgart → Porto
    (0, 3),  # Oslo → Split
    (7, 1),  # Stockholm → Stuttgart
    (0, 4),  # Oslo → Geneva
    (7, 3),  # Stockholm → Split
    (3, 1),  # Split → Stuttgart
    (6, 0),  # Tallinn → Oslo
    (7, 4),  # Stockholm → Geneva
    (0, 5),  # Oslo → Porto
    (4, 5),  # Geneva → Porto
    (4, 3),  # Geneva → Split
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(21)]

solver = Solver()

# Add domain constraints for each day
for i in range(21):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 7)

# Add specific day constraints
solver.add(days[0] == 2)  # Day 1: Reykjavik
solver.add(days[1] == 2)  # Day 2: Reykjavik
solver.add(days[18] == 5) # Day 19: Porto
solver.add(days[19] == 5) # Day 20: Porto
solver.add(days[20] == 5) # Day 21: Porto

# Add Stockholm meeting constraint (days 3 or 4)
solver.add(Or(days[2] == 7, days[3] == 7))

# Add transition constraints
for i in range(20):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(21)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(21):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")