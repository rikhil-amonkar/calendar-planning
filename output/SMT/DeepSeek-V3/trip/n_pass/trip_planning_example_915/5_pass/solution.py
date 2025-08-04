import json
from z3 import *

# Define cities and their codes
cities = {
    'Bucharest': 0,
    'Venice': 1,
    'Prague': 2,
    'Frankfurt': 3,
    'Zurich': 4,
    'Florence': 5,
    'Tallinn': 6
}
city_names = {v: k for k, v in cities.items()}

# Direct flights adjacency
direct_flights = {
    0: [2, 3, 4],  # Bucharest
    1: [3, 4],      # Venice
    2: [0, 3, 4, 5, 6],  # Prague
    3: [0, 1, 2, 4, 5, 6],  # Frankfurt
    4: [0, 1, 2, 3, 5, 6],  # Zurich
    5: [2, 3, 4],   # Florence
    6: [2, 3, 4]    # Tallinn
}

total_days = 26

solver = Solver()

# Day variables
days = [Int(f'day_{i}') for i in range(1, total_days + 1)]
for day in days:
    solver.add(day >= 0, day <= 6)

# Fixed date constraints
for day in range(22, 27):  # Venice days 22-26
    solver.add(days[day-1] == cities['Venice'])
for day in range(12, 17):  # Frankfurt days 12-16
    solver.add(days[day-1] == cities['Frankfurt'])
for day in range(8, 13):   # Tallinn days 8-12
    solver.add(days[day-1] == cities['Tallinn'])

# Flight transitions - more efficient encoding
for i in range(total_days - 1):
    current = days[i]
    next_c = days[i+1]
    # Either stay or fly to connected city
    solver.add(Or(
        current == next_c,
        *[And(current == src, next_c == dst) 
          for src in direct_flights for dst in direct_flights[src]]
    ))

# Total days per city (including flight days)
day_counts = {city: 0 for city in cities}
for city in cities:
    count = Sum([If(days[i] == cities[city], 1, 0) 
                for i in range(total_days)])
    solver.add(count == {
        'Bucharest': 3,
        'Venice': 5,
        'Prague': 4,
        'Frankfurt': 5,
        'Zurich': 5,
        'Florence': 5,
        'Tallinn': 5
    }[city])

# Additional constraints to help the solver
# Ensure we don't have impossible sequences
for i in range(total_days - 2):
    solver.add(Not(And(
        days[i] != days[i+1],
        days[i+1] != days[i+2],
        days[i] == days[i+2]
    )))

if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(total_days):
        city_code = model.evaluate(days[i]).as_long()
        itinerary.append({
            "day": i+1,
            "place": city_names[city_code]
        })
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found - constraints may be too restrictive")