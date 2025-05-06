from z3 import *

# Define cities and their required days
cities = {
    0: 'Riga',
    1: 'Frankfurt',
    2: 'Amsterdam',
    3: 'Vilnius',
    4: 'London',
    5: 'Stockholm',
    6: 'Bucharest'
}

required_days = {
    0: 2,
    1: 3,
    2: 2,
    3: 5,
    4: 2,
    5: 3,
    6: 4
}

# Define allowed transitions between cities
allowed_transitions = [
    (4, 2),  # London → Amsterdam
    (3, 1),  # Vilnius → Frankfurt
    (0, 3),  # Riga → Vilnius
    (0, 5),  # Riga → Stockholm
    (4, 6),  # London → Bucharest
    (2, 5),  # Amsterdam → Stockholm
    (2, 1),  # Amsterdam → Frankfurt
    (1, 5),  # Frankfurt → Stockholm
    (6, 0),  # Bucharest → Riga
    (2, 0),  # Amsterdam → Riga
    (2, 6),  # Amsterdam → Bucharest
    (0, 1),  # Riga → Frankfurt
    (6, 1),  # Bucharest → Frankfurt
    (4, 1),  # London → Frankfurt
    (4, 5),  # London → Stockholm
    (2, 3)   # Amsterdam → Vilnius
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(15)]

solver = Solver()

# Add domain constraints for each day
for i in range(15):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 6)

# Add specific day constraints
# Meet a friend in Amsterdam between day 2 and day 3
solver.add(Or([days[i] == 2 for i in [1, 2]]))
# Attend workshop in Vilnius between day 7 and day 11
for i in range(6, 11):
    solver.add(days[i] == 3)
# Attend wedding in Stockholm between day 13 and day 15
for i in range(12, 15):
    solver.add(days[i] == 5)

# Add transition constraints
for i in range(14):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(15)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(15):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")