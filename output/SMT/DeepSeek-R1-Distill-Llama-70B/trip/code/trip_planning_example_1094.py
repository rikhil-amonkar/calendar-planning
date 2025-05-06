from z3 import *

# Define cities and their required days
cities = {
    0: 'Vienna',
    1: 'Barcelona',
    2: 'Edinburgh',
    3: 'Krakow',
    4: 'Riga',
    5: 'Hamburg',
    6: 'Paris',
    7: 'Stockholm'
}

required_days = {
    0: 4,
    1: 2,
    2: 4,
    3: 3,
    4: 4,
    5: 2,
    6: 2,
    7: 2
}

# Define allowed transitions between cities
allowed_transitions = [
    (5, 7),  # Hamburg → Stockholm
    (0, 7),  # Vienna → Stockholm
    (6, 2),  # Paris → Edinburgh
    (4, 1),  # Riga → Barcelona
    (6, 4),  # Paris → Riga
    (3, 1),  # Krakow → Barcelona
    (2, 7),  # Edinburgh → Stockholm
    (6, 3),  # Paris → Krakow
    (3, 7),  # Krakow → Stockholm
    (4, 2),  # Riga → Edinburgh
    (1, 7),  # Barcelona → Stockholm
    (6, 7),  # Paris → Stockholm
    (3, 2),  # Krakow → Edinburgh
    (0, 5),  # Vienna → Hamburg
    (6, 5),  # Paris → Hamburg
    (4, 7),  # Riga → Stockholm
    (5, 1),  # Hamburg → Barcelona
    (0, 1),  # Vienna → Barcelona
    (3, 0),  # Krakow → Vienna
    (4, 5),  # Riga → Hamburg
    (1, 2),  # Barcelona → Edinburgh
    (6, 1),  # Paris → Barcelona
    (5, 2),  # Hamburg → Edinburgh
    (6, 0),  # Paris → Vienna
    (0, 4),  # Vienna → Riga
    (0, 3)   # Vienna → Krakow
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(16)]

solver = Solver()

# Add domain constraints for each day
for i in range(16):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 7)

# Add specific day constraints
# Attend wedding in Paris between day 1 and day 2
solver.add(days[0] == 6)
solver.add(days[1] == 6)
# Attend conference in Hamburg on day 10 and day 11
solver.add(days[9] == 5)
solver.add(days[10] == 5)
# Meet a friend in Edinburgh between day 12 and day 15
solver.add(Or([days[i] == 2 for i in range(11, 15)]))
# Visit relatives in Stockholm between day 15 and day 16
solver.add(days[14] == 7)
solver.add(days[15] == 7)

# Add transition constraints
for i in range(15):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(16)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(16):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")