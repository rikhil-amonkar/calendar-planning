from z3 import *

# Define cities and their required days
cities = {
    0: 'Paris',
    1: 'Warsaw',
    2: 'Krakow',
    3: 'Tallinn',
    4: 'Riga',
    5: 'Copenhagen',
    6: 'Helsinki',
    7: 'Oslo',
    8: 'Santorini',
    9: 'Lyon'
}

required_days = {
    0: 5,
    1: 2,
    2: 2,
    3: 2,
    4: 2,
    5: 5,
    6: 5,
    7: 5,
    8: 2,
    9: 4
}

# Define allowed transitions between cities
allowed_transitions = [
    (1, 4), (1, 3), (5, 6), (9, 0), (5, 1), (9, 7), (0, 7), (0, 4), (0, 3),
    (7, 4), (2, 6), (0, 3), (5, 2), (5, 4), (5, 7), (5, 5), (5, 3),
    (7, 3), (7, 6), (5, 3), (7, 1), (8, 7), (7, 1), (0, 5), (0, 1),
    (8, 7), (5, 9), (6, 1), (6, 4), (6, 5), (6, 7), (5, 9), (5, 7),
    (0, 5), (0, 1), (5, 7), (5, 1)
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(25)]

solver = Solver()

# Add domain constraints for each day
for i in range(25):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 9)

# Add specific day constraints
# Meet friends in Paris between day 4 and day 8
for i in range(3, 8):
    solver.add(days[i] == 0)
# Attend workshop in Krakow on day 17 and day 18
solver.add(days[16] == 2)
solver.add(days[17] == 2)
# Attend wedding in Riga on day 23 and day 24
solver.add(days[22] == 4)
solver.add(days[23] == 4)
# Meet a friend in Helsinki between day 18 and day 22
for i in range(17, 22):
    solver.add(days[i] == 6)
# Visit relatives in Santorini on day 12 and day 13
solver.add(days[11] == 8)
solver.add(days[12] == 8)

# Add transition constraints
for i in range(24):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(25)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(25):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")