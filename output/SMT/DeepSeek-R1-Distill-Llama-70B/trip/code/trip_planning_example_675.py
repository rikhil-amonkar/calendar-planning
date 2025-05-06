from z3 import *

# Define cities and their required days
cities = {
    0: 'Dubrovnik',
    1: 'Split',
    2: 'Milan',
    3: 'Porto',
    4: 'Krakow',
    5: 'Munich'
}

required_days = {
    0: 4,
    1: 3,
    2: 3,
    3: 4,
    4: 2,
    5: 5
}

# Define allowed transitions between cities
allowed_transitions = [
    (5, 3),  # Munich → Porto
    (1, 2),  # Split → Milan
    (2, 3),  # Milan → Porto
    (5, 4),  # Munich → Krakow
    (5, 2),  # Munich → Milan
    (0, 5),  # Dubrovnik → Munich
    (4, 1),  # Krakow → Split
    (4, 2),  # Krakow → Milan
    (5, 1)   # Munich → Split
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(16)]

solver = Solver()

# Add domain constraints for each day
for i in range(16):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 5)

# Add specific day constraints
# Annual show in Munich from day 4 to day 8
for i in range(3, 8):
    solver.add(days[i] == 5)
# Attend wedding in Milan between day 11 and day 13
for i in range(10, 13):
    solver.add(days[i] == 2)
# Meet friends in Krakow between day 8 and day 9
solver.add(days[7] == 4)
solver.add(days[8] == 4)

# Add transition constraints
for i in range(15):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(16)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(16):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")