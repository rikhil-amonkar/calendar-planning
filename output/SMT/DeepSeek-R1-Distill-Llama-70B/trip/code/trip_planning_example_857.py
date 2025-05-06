from z3 import *

# Define cities and their required days
cities = {
    0: 'Porto',
    1: 'Geneva',
    2: 'Mykonos',
    3: 'Manchester',
    4: 'Hamburg',
    5: 'Naples',
    6: 'Frankfurt'
}

required_days = {
    0: 2,
    1: 3,
    2: 3,
    3: 4,
    4: 5,
    5: 5,
    6: 2
}

# Define allowed transitions between cities
allowed_transitions = [
    (4, 6),  # Hamburg → Frankfurt
    (5, 2),  # Naples → Mykonos
    (4, 0),  # Hamburg → Porto
    (4, 1),  # Hamburg → Geneva
    (2, 1),  # Mykonos → Geneva
    (6, 1),  # Frankfurt → Geneva
    (6, 0),  # Frankfurt → Porto
    (1, 0),  # Geneva → Porto
    (1, 3),  # Geneva → Manchester
    (5, 3),  # Naples → Manchester
    (6, 5),  # Frankfurt → Naples
    (6, 3),  # Frankfurt → Manchester
    (5, 1),  # Naples → Geneva
    (0, 3),  # Porto → Manchester
    (4, 3)   # Hamburg → Manchester
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(18)]

solver = Solver()

# Add domain constraints for each day
for i in range(18):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 6)

# Add specific day constraints
# Annual show in Frankfurt on day 5 and day 6
solver.add(days[4] == 6)
solver.add(days[5] == 6)
# Meet a friend in Mykonos between day 10 and day 12
for i in range(9, 12):
    solver.add(days[i] == 2)
# Attend wedding in Manchester between day 15 and day 18
for i in range(14, 18):
    solver.add(days[i] == 3)

# Add transition constraints
for i in range(17):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(18)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(18):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")