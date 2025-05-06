from z3 import *

# Define cities and their required days
cities = {
    0: 'Venice',
    1: 'Reykjavik',
    2: 'Munich',
    3: 'Santorini',
    4: 'Manchester',
    5: 'Porto',
    6: 'Bucharest',
    7: 'Tallinn',
    8: 'Valencia',
    9: 'Vienna'
}

required_days = {
    0: 3,
    1: 2,
    2: 3,
    3: 3,
    4: 3,
    5: 3,
    6: 5,
    7: 4,
    8: 2,
    9: 5
}

# Define allowed transitions between cities
allowed_transitions = [
    (6, 4), (2, 0), (3, 4), (9, 1), (0, 3), (2, 5), (8, 9), (4, 9),
    (5, 9), (0, 4), (3, 9), (2, 4), (2, 1), (6, 8), (0, 9), (6, 9),
    (5, 4), (2, 9), (8, 5), (2, 6), (7, 2), (3, 6), (2, 8)
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(24)]

solver = Solver()

# Add domain constraints for each day
for i in range(24):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 9)

# Add specific day constraints
# Munich between day 4 and day 6
solver.add(Or([days[i] == 2 for i in range(3, 6)]))
# Santorini between day 8 and day 10
solver.add(Or([days[i] == 3 for i in range(7, 10)]))
# Valencia on days 14 and 15
solver.add(days[13] == 8)
solver.add(days[14] == 8)

# Add transition constraints
for i in range(23):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(24)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(24):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")