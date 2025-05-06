from z3 import *

# Define cities and their required days
cities = {
    0: 'Krakow',
    1: 'Dubrovnik',
    2: 'Frankfurt'
}

required_days = {
    0: 2,
    1: 7,
    2: 3
}

# Define allowed transitions between cities
allowed_transitions = [
    (2, 0),  # Frankfurt → Krakow
    (1, 2)   # Dubrovnik → Frankfurt
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(10)]

solver = Solver()

# Add domain constraints for each day
for i in range(10):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 2)

# Add specific day constraints
# Attend wedding in Krakow on day 9 and day 10
solver.add(days[8] == 0)
solver.add(days[9] == 0)

# Add transition constraints
for i in range(9):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(10)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(10):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")