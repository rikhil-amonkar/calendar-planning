from z3 import *

# Define cities and their required days
cities = {
    0: 'Tallinn',
    1: 'Bucharest',
    2: 'Seville',
    3: 'Stockholm',
    4: 'Munich',
    5: 'Milan'
}

required_days = {
    0: 2,
    1: 4,
    2: 5,
    3: 5,
    4: 5,
    5: 2
}

# Define allowed transitions between cities
allowed_transitions = [
    (5, 3),  # Milan → Stockholm
    (4, 3),  # Munich → Stockholm
    (1, 4),  # Bucharest → Munich
    (4, 2),  # Munich → Seville
    (3, 0),  # Stockholm → Tallinn
    (4, 5),  # Munich → Milan
    (4, 0),  # Munich → Tallinn
    (2, 5)   # Seville → Milan
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
    solver.add(days[i] <= 5)

# Add specific day constraints
# Attend event in Bucharest between day 1 and day 4
for i in range(4):
    solver.add(days[i] == 1)
# Attend wedding in Munich between day 4 and day 8
for i in range(4, 8):
    solver.add(days[i] == 4)
# Meet friends in Seville between day 8 and day 12
for i in range(7, 12):
    solver.add(days[i] == 2)

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