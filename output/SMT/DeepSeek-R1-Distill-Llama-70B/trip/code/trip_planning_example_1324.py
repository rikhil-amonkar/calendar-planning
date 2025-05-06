from z3 import *

# Define cities and their required days
cities = {
    0: 'Venice',
    1: 'Barcelona',
    2: 'Copenhagen',
    3: 'Lyon',
    4: 'Reykjavik',
    5: 'Dubrovnik',
    6: 'Athens',
    7: 'Tallinn',
    8: 'Munich'
}

required_days = {
    0: 4,
    1: 3,
    2: 4,
    3: 4,
    4: 4,
    5: 5,
    6: 2,
    7: 5,
    8: 3
}

# Define allowed transitions between cities
allowed_transitions = [
    (2, 6),  # Copenhagen → Athens
    (2, 5),  # Copenhagen → Dubrovnik
    (8, 7),  # Munich → Tallinn
    (2, 8),  # Copenhagen → Munich
    (0, 8),  # Venice → Munich
    (4, 6),  # Reykjavik → Athens
    (6, 5),  # Athens → Dubrovnik
    (0, 6),  # Venice → Athens
    (3, 1),  # Lyon → Barcelona
    (2, 4),  # Copenhagen → Reykjavik
    (4, 8),  # Reykjavik → Munich
    (6, 8),  # Athens → Munich
    (3, 8),  # Lyon → Munich
    (1, 4),  # Barcelona → Reykjavik
    (5, 8),  # Dubrovnik → Munich
    (1, 6),  # Barcelona → Athens
    (2, 1),  # Copenhagen → Barcelona
    (0, 1),  # Venice → Barcelona
    (1, 8),  # Barcelona → Munich
    (1, 7),  # Barcelona → Tallinn
    (2, 7)   # Copenhagen → Tallinn
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(26)]

solver = Solver()

# Add domain constraints for each day
for i in range(26):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 8)

# Add specific day constraints
# Meet a friend in Barcelona between day 10 and day 12
for i in range(9, 12):
    solver.add(days[i] == 1)
# Visit relatives in Copenhagen between day 7 and day 10
for i in range(6, 10):
    solver.add(days[i] == 2)
# Attend wedding in Dubrovnik between day 16 and day 20
for i in range(15, 20):
    solver.add(days[i] == 5)

# Add transition constraints
for i in range(25):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(26)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(26):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")