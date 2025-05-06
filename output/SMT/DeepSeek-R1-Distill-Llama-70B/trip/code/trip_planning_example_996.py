from z3 import *

# Define cities and their required days
cities = {
    0: 'Valencia',
    1: 'Riga',
    2: 'Prague',
    3: 'Mykonos',
    4: 'Zurich',
    5: 'Bucharest',
    6: 'Nice'
}

required_days = {
    0: 5,
    1: 5,
    2: 3,
    3: 3,
    4: 5,
    5: 5,
    6: 2
}

# Define allowed transitions between cities
allowed_transitions = [
    (3, 6),  # Mykonos → Nice
    (3, 4),  # Mykonos → Zurich
    (2, 5),  # Prague → Bucharest
    (0, 5),  # Valencia → Bucharest
    (4, 2),  # Zurich → Prague
    (1, 6),  # Riga → Nice
    (4, 1),  # Zurich → Riga
    (4, 5),  # Zurich → Bucharest
    (4, 0),  # Zurich → Valencia
    (5, 1),  # Bucharest → Riga
    (2, 1),  # Prague → Riga
    (2, 0),  # Prague → Valencia
    (4, 6)   # Zurich → Nice
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
# Wedding in Mykonos between day 1 and day 3
for i in range(3):
    solver.add(days[i] == 3)
# Visit relatives in Prague between day 7 and day 9
for i in range(6, 9):
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