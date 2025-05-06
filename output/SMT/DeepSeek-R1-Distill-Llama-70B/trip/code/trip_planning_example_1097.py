from z3 import *

# Define cities and their required days
cities = {
    0: 'Reykjavik',
    1: 'Riga',
    2: 'Oslo',
    3: 'Lyon',
    4: 'Dubrovnik',
    5: 'Madrid',
    6: 'Warsaw',
    7: 'London'
}

required_days = {
    0: 4,
    1: 2,
    2: 3,
    3: 5,
    4: 2,
    5: 2,
    6: 4,
    7: 3
}

# Define allowed transitions between cities
allowed_transitions = [
    (6, 0), (2, 5), (6, 1), (3, 7), (5, 7), (6, 7), (0, 5), (6, 2),
    (2, 4), (2, 0), (1, 2), (2, 3), (2, 7), (7, 0), (6, 5), (5, 3),
    (4, 5)
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
    solver.add(days[i] <= 7)

# Add specific day constraints
# Riga on days 4 and 5
solver.add(days[3] == 1)
solver.add(days[4] == 1)

# Dubrovnik on days 7 and 8
solver.add(days[6] == 4)
solver.add(days[7] == 4)

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