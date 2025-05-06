from z3 import *

# Define cities and their required days
cities = {
    0: 'Berlin',
    1: 'Nice',
    2: 'Athens',
    3: 'Stockholm',
    4: 'Barcelona',
    5: 'Vilnius',
    6: 'Lyon'
}

required_days = {
    0: 3,
    1: 5,
    2: 5,
    3: 5,
    4: 2,
    5: 4,
    6: 2
}

# Define allowed transitions between cities
allowed_transitions = [
    (6, 1),  # Lyon → Nice
    (3, 2),  # Stockholm → Athens
    (1, 2),  # Nice → Athens
    (0, 2),  # Berlin → Athens
    (0, 1),  # Berlin → Nice
    (0, 4),  # Berlin → Barcelona
    (0, 5),  # Berlin → Vilnius
    (4, 1),  # Barcelona → Nice
    (2, 5),  # Athens → Vilnius
    (0, 3),  # Berlin → Stockholm
    (1, 3),  # Nice → Stockholm
    (4, 2),  # Barcelona → Athens
    (4, 3),  # Barcelona → Stockholm
    (4, 6)   # Barcelona → Lyon
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
    solver.add(days[i] <= 6)

# Add specific day constraints
# Conference in Berlin on day 1 and day 3
solver.add(days[0] == 0)
solver.add(days[2] == 0)
# Workshop in Barcelona on day 3 and day 4
solver.add(days[2] == 4)
solver.add(days[3] == 4)
# Wedding in Lyon on day 4 and day 5
solver.add(days[3] == 6)
solver.add(days[4] == 6)

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