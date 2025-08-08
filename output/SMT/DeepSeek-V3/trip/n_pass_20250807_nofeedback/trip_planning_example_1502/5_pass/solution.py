import json
from z3 import *

# Define the cities with their indices
cities = {
    "Santorini": 0,
    "Valencia": 1,
    "Madrid": 2,
    "Seville": 3,
    "Bucharest": 4,
    "Vienna": 5,
    "Riga": 6,
    "Tallinn": 7,
    "Krakow": 8,
    "Frankfurt": 9
}

# Define flight connections as a set of tuples
flight_connections = [
    (5, 4), (5, 3), (5, 1), (5, 2), (5, 8), (5, 9), (5, 6),  # Vienna
    (4, 5), (4, 6), (4, 1), (4, 0), (4, 2), (4, 9),           # Bucharest
    (0, 2), (0, 4), (0, 5),                                    # Santorini
    (2, 0), (2, 1), (2, 3), (2, 5), (2, 4), (2, 9),            # Madrid
    (3, 1), (3, 5), (3, 2),                                    # Seville
    (1, 3), (1, 2), (1, 4), (1, 5), (1, 8), (1, 9),            # Valencia
    (6, 4), (6, 5), (6, 7), (6, 9),                            # Riga
    (7, 6), (7, 9),                                             # Tallinn
    (8, 1), (8, 9), (8, 5),                                    # Krakow
    (9, 1), (9, 8), (9, 5), (9, 6), (9, 7), (9, 4), (9, 2)     # Frankfurt
]

# Create flight matrix
flight_matrix = [[False for _ in range(10)] for _ in range(10)]
for (i, j) in flight_connections:
    flight_matrix[i][j] = True
    flight_matrix[j][i] = True  # Assuming flights are bidirectional

# Create solver
s = Solver()

# Day variables (1-27)
day_vars = [Int(f"day_{i}") for i in range(1, 28)]
for day in day_vars:
    s.add(day >= 0, day < 10)

# City day requirements
city_days = {
    0: 3,  # Santorini
    1: 4,  # Valencia
    2: 2,  # Madrid
    3: 2,  # Seville
    4: 3,  # Bucharest
    5: 4,  # Vienna
    6: 4,  # Riga
    7: 5,  # Tallinn
    8: 5,  # Krakow
    9: 4   # Frankfurt
}

for city, days in city_days.items():
    s.add(Sum([If(day_vars[i] == city, 1, 0) for i in range(27)]) == days)

# Fixed events
# Madrid days 6-7 (0-based 5-6)
s.add(day_vars[5] == 2)
s.add(day_vars[6] == 2)

# Vienna wedding days 3-6 (0-based 2-5)
for i in range(2, 6):
    s.add(day_vars[i] == 5)

# Riga conference days 20-23 (0-based 19-22)
for i in range(19, 23):
    s.add(day_vars[i] == 6)

# Tallinn workshop days 23-27 (0-based 22-26)
for i in range(22, 27):
    s.add(day_vars[i] == 7)

# Krakow friends days 11-15 (0-based 10-14)
for i in range(10, 15):
    s.add(day_vars[i] == 8)

# Flight transitions
for i in range(26):
    current = day_vars[i]
    next_day = day_vars[i+1]
    s.add(Or(
        current == next_day,
        *[And(current == c1, next_day == c2) for c1 in range(10) for c2 in range(10) if flight_matrix[c1][c2]]
    ))

# Try to find a solution
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(27):
        day = i + 1
        city_index = m.evaluate(day_vars[i]).as_long()
        city_name = [k for k, v in cities.items() if v == city_index][0]
        itinerary.append({"day": day, "place": city_name})
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No valid itinerary found.")