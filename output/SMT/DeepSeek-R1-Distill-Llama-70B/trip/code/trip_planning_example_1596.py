from z3 import *

# Define cities and their required days
cities = {
    0: 'Bucharest',
    1: 'Krakow',
    2: 'Munich',
    3: 'Barcelona',
    4: 'Warsaw',
    5: 'Budapest',
    6: 'Stockholm',
    7: 'Riga',
    8: 'Edinburgh',
    9: 'Vienna'
}

required_days = {
    0: 2,
    1: 4,
    2: 3,
    3: 5,
    4: 5,
    5: 5,
    6: 2,
    7: 5,
    8: 5,
    9: 5
}

# Define allowed transitions between cities
allowed_transitions = [
    (5, 2),  # Budapest → Munich
    (0, 7),  # Bucharest → Riga
    (2, 1),  # Munich → Krakow
    (2, 4),  # Munich → Warsaw
    (2, 0),  # Munich → Bucharest
    (8, 6),  # Edinburgh → Stockholm
    (3, 4),  # Barcelona → Warsaw
    (8, 1),  # Edinburgh → Krakow
    (3, 2),  # Barcelona → Munich
    (6, 1),  # Stockholm → Krakow
    (5, 9),  # Budapest → Vienna
    (3, 6),  # Barcelona → Stockholm
    (6, 2),  # Stockholm → Munich
    (8, 5),  # Edinburgh → Budapest
    (3, 7),  # Barcelona → Riga
    (8, 3),  # Edinburgh → Barcelona
    (9, 7),  # Vienna → Riga
    (3, 5),  # Barcelona → Budapest
    (0, 4),  # Bucharest → Warsaw
    (9, 1),  # Vienna → Krakow
    (8, 2),  # Edinburgh → Munich
    (3, 0),  # Barcelona → Bucharest
    (8, 7),  # Edinburgh → Riga
    (9, 6),  # Vienna → Stockholm
    (4, 1),  # Warsaw → Krakow
    (3, 1),  # Barcelona → Krakow
    (7, 2),  # Riga → Munich
    (9, 0),  # Vienna → Bucharest
    (5, 4),  # Budapest → Warsaw
    (9, 4),  # Vienna → Warsaw
    (3, 9),  # Barcelona → Vienna
    (5, 0),  # Budapest → Bucharest
    (9, 2),  # Vienna → Munich
    (7, 4),  # Riga → Warsaw
    (6, 7),  # Stockholm → Riga
    (6, 4)   # Stockholm → Warsaw
]

# Build neighbors dictionary
neighbors = {}
for a, b in allowed_transitions:
    if a not in neighbors:
        neighbors[a] = []
    neighbors[a].append(b)

# Create day variables
days = [Int(f"day_{i}") for i in range(32)]

solver = Solver()

# Add domain constraints for each day
for i in range(32):
    solver.add(days[i] >= 0)
    solver.add(days[i] <= 9)

# Add specific day constraints
# Meet a friend in Edinburgh between day 1 and day 5
for i in range(5):
    solver.add(days[i] == 8)
# Annual show in Budapest between day 9 and day 13
for i in range(8, 13):
    solver.add(days[i] == 5)
# Attend workshop in Munich between day 18 and day 20
for i in range(17, 20):
    solver.add(days[i] == 2)
# Attend conference in Warsaw between day 25 and day 29
for i in range(24, 29):
    solver.add(days[i] == 4)
# Meet friends in Stockholm between day 17 and day 18
for i in range(16, 18):
    solver.add(days[i] == 6)

# Add transition constraints
for i in range(31):
    a = days[i]
    b = days[i+1]
    for city in neighbors:
        if city == a:
            continue
        # If current day is 'city', next day must be in its neighbors
        solver.add(Implies(a == city, Or([b == neighbor for neighbor in neighbors.get(city, [])])))

# Add count constraints for each city
for c in required_days:
    solver.add(PbEq([(days[i] == c, 1) for i in range(32)], required_days[c]))

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    print("Trip Plan:")
    for i in range(32):
        day = model[days[i]].as_long()
        print(f"Day {i+1}: {cities[day]}")
else:
    print("No valid trip plan found.")