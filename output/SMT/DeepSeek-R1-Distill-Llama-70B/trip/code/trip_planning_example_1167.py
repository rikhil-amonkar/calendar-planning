from z3 import *

# Define cities and their required days
cities = {
    0: 'Dublin',
    1: 'Krakow',
    2: 'Istanbul',
    3: 'Venice',
    4: 'Naples',
    5: 'Brussels',
    6: 'Mykonos',
    7: 'Frankfurt'
}

required_days = {
    0: 5,
    1: 4,
    2: 3,
    3: 3,
    4: 4,
    5: 2,
    6: 4,
    7: 3
}

# Define allowed transitions between cities
allowed_transitions = [
    (0, 5),  # Dublin → Brussels
    (6, 4),  # Mykonos → Naples
    (3, 2),  # Venice → Istanbul
    (7, 1),  # Frankfurt → Krakow
    (4, 0),  # Naples → Dublin
    (1, 5),  # Krakow → Brussels
    (4, 2),  # Naples → Istanbul
    (4, 5),  # Naples → Brussels
    (2, 7),  # Istanbul → Frankfurt
    (5, 7),  # Brussels → Frankfurt
    (2, 1),  # Istanbul → Krakow
    (2, 5),  # Istanbul → Brussels
    (3, 7),  # Venice → Frankfurt
    (4, 7),  # Naples → Frankfurt
    (0, 1),  # Dublin → Krakow
    (3, 5),  # Venice → Brussels
    (4, 3),  # Naples → Venice
    (2, 0),  # Istanbul → Dublin
    (3, 0),  # Venice → Dublin
    (0, 7)   # Dublin → Frankfurt
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
# Annual show in Dublin between day 11 and day 15
for i in range(10, 15):
    solver.add(days[i] == 0)
# Meet a friend in Istanbul between day 9 and day 11
for i in range(8, 11):
    solver.add(days[i] == 2)
# Visit relatives in Mykonos between day 1 and day 4
for i in range(3):
    solver.add(days[i] == 6)
# Meet friends in Frankfurt between day 15 and day 17
for i in range(14, 17):
    solver.add(days[i] == 7)

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