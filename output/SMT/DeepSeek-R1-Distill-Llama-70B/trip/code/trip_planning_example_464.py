from z3 import *

# Define cities and their required days
cities = {
    0: 'Krakow',
    1: 'Frankfurt',
    2: 'Oslo',
    3: 'Dubrovnik',
    4: 'Naples'
}

required_days = {
    0: 5,
    1: 4,
    2: 3,
    3: 5,
    4: 5
}

# Define allowed transitions between cities
allowed_transitions = [
    (3, 2),  # Dubrovnik → Oslo
    (1, 0),  # Frankfurt → Krakow
    (1, 2),  # Frankfurt → Oslo
    (3, 1),  # Dubrovnik → Frankfurt
    (0, 2),  # Krakow → Oslo
    (4, 2),  # Naples → Oslo
    (4, 3),  # Naples → Dubrovnik
    (4, 1)   # Naples → Frankfurt
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
    solver.add(days[i] <= 4)

# Add specific day constraints
# Oslo on days 16, 17, and 18
solver.add(days[15] == 2)
solver.add(days[16] == 2)
solver.add(days[17] == 2)

# Dubrovnik between days 5 and 9
for i in range(4, 9):
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