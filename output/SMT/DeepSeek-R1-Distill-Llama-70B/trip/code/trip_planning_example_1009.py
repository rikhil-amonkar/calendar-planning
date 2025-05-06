from z3 import *

# Define cities and their required days
cities = {
    0: 'Riga',
    1: 'Manchester',
    2: 'Bucharest',
    3: 'Florence',
    4: 'Vienna',
    5: 'Istanbul',
    6: 'Reykjavik',
    7: 'Stuttgart'
}

required_days = {
    0: 4,
    1: 5,
    2: 4,
    3: 4,
    4: 2,
    5: 2,
    6: 4,
    7: 5
}

# Define allowed transitions between cities
allowed_transitions = [
    (2, 4),  # Bucharest → Vienna
    (6, 4),  # Reykjavik → Vienna
    (1, 4),  # Manchester → Vienna
    (1, 0),  # Manchester → Riga
    (0, 4),  # Riga → Vienna
    (5, 4),  # Istanbul → Vienna
    (4, 3),  # Vienna → Florence
    (7, 4),  # Stuttgart → Vienna
    (0, 2),  # Riga → Bucharest
    (5, 0),  # Istanbul → Riga
    (7, 5),  # Stuttgart → Istanbul
    (6, 7),  # Reykjavik → Stuttgart
    (5, 2),  # Istanbul → Bucharest
    (1, 5),  # Manchester → Istanbul
    (1, 2),  # Manchester → Bucharest
    (7, 1)   # Stuttgart → Manchester
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(23)]

solver = Solver()

# Add domain constraints for each day
for i in range(23):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 7)

# Add specific day constraints
# Annual show in Istanbul on day 12 and day 13
solver.add(days[11] == 5)
solver.add(days[12] == 5)
# Workshop in Bucharest between day 16 and day 19
for i in range(15, 19):
    solver.add(days[i] == 2)

# Add transition constraints
for i in range(22):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(23)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(23):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")