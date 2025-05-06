from z3 import *

# Define cities and their required days
cities = {
    0: 'Dubrovnik',
    1: 'Warsaw',
    2: 'Stuttgart',
    3: 'Bucharest',
    4: 'Copenhagen'
}

required_days = {
    0: 5,
    1: 2,
    2: 7,
    3: 6,
    4: 3
}

# Define allowed transitions between cities
allowed_transitions = [
    (1, 4),  # Warsaw → Copenhagen
    (2, 4),  # Stuttgart → Copenhagen
    (1, 2),  # Warsaw → Stuttgart
    (3, 4),  # Bucharest → Copenhagen
    (3, 1),  # Bucharest → Warsaw
    (4, 0)   # Copenhagen → Dubrovnik
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(19)]

solver = Solver()

# Add domain constraints for each day
for i in range(19):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 4)

# Add specific day constraints
# Attend wedding in Bucharest between day 1 and day 6
solver.add(Or([days[i] == 3 for i in range(6)]))
# Attend conference in Stuttgart on day 7 and day 13
solver.add(days[6] == 2)
solver.add(days[12] == 2)

# Add transition constraints
for i in range(18):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(19)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(19):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")