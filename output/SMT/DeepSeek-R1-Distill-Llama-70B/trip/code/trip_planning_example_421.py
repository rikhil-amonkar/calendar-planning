from z3 import *

# Define cities and their required days
cities = {
    0: 'Nice',
    1: 'Krakow',
    2: 'Dublin',
    3: 'Lyon',
    4: 'Frankfurt'
}

required_days = {
    0: 5,
    1: 6,
    2: 7,
    3: 4,
    4: 2
}

# Define allowed transitions between cities
allowed_transitions = [
    (0, 2),  # Nice → Dublin
    (2, 4),  # Dublin → Frankfurt
    (2, 1),  # Dublin → Krakow
    (1, 4),  # Krakow → Frankfurt
    (3, 4),  # Lyon → Frankfurt
    (0, 4),  # Nice → Frankfurt
    (3, 2),  # Lyon → Dublin
    (0, 3)   # Nice → Lyon
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(20)]

solver = Solver()

# Add domain constraints for each day
for i in range(20):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 4)

# Add specific day constraints
# Must be in Nice at least once between day 1 and day 5
solver.add(Or([days[i] == 0 for i in range(5)]))
# Must be in Frankfurt on days 19 and 20
solver.add(days[18] == 4)
solver.add(days[19] == 4)

# Add transition constraints
for i in range(19):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(20)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(20):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")