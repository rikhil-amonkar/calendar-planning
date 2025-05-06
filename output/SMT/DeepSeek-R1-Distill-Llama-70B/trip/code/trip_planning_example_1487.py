from z3 import *

# Define cities and their required days
cities = {
    0: 'Copenhagen',
    1: 'Dubrovnik',
    2: 'Brussels',
    3: 'Geneva',
    4: 'Mykonos',
    5: 'Naples',
    6: 'Prague',
    7: 'Athens',
    8: 'Santorini',
    9: 'Munich'
}

required_days = {
    0: 5,
    1: 3,
    2: 4,
    3: 3,
    4: 2,
    5: 4,
    6: 2,
    7: 4,
    8: 5,
    9: 5
}

# Define allowed transitions between cities
allowed_transitions = [
    (0, 1), (2, 0), (6, 3), (7, 3), (5, 1), (7, 1), (3, 4), (5, 4),
    (5, 9), (7, 4), (6, 7), (0, 9), (5, 7), (6, 0), (2, 5), (2, 9),
    (7, 9), (2, 7), (7, 9), (3, 9), (9, 4), (0, 9), (2, 3), (0, 3),
    (6, 9), (0, 8), (5, 8), (3, 1)
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(28)]

solver = Solver()

# Add domain constraints for each day
for i in range(28):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 9)

# Add specific day constraints
# Mykonos on days 27 and 28
solver.add(days[26] == 4)
solver.add(days[27] == 4)

# Naples between days 5 and 8
solver.add(Or([days[i] == 5 for i in range(4, 8)]))

# Athens between days 8 and 11
solver.add(Or([days[i] == 7 for i in range(7, 11)]))

# Copenhagen between days 11 and 15
solver.add(Or([days[i] == 0 for i in range(10, 15)]))

# Add transition constraints
for i in range(27):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(28)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(28):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")