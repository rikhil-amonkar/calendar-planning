#!/usr/bin/env python3
from z3 import *
import json

# City definitions (index: name & duration)
# 0: Lyon (3 days)
# 1: Paris (5 days)
# 2: Riga (2 days)
# 3: Berlin (2 days)
# 4: Stockholm (3 days)
# 5: Zurich (5 days)
# 6: Nice (2 days)
# 7: Seville (3 days)
# 8: Milan (3 days)
# 9: Naples (4 days)
cities = ["Lyon", "Paris", "Riga", "Berlin", "Stockholm", 
          "Zurich", "Nice", "Seville", "Milan", "Naples"]
durations = [3, 5, 2, 2, 3, 5, 2, 3, 3, 4]

# Allowed direct flights (neighbors) for each city (using indices)
allowed_neighbors = {
    0: [1, 6],
    1: [0, 2, 3, 4, 5, 6, 7, 8, 9],
    2: [1, 3, 4, 6, 8],
    3: [1, 2, 4, 6, 8, 9],
    4: [1, 2, 3, 5, 6, 8],
    5: [1, 2, 4, 6, 8, 9],
    6: [0, 1, 2, 3, 4, 5, 9],
    # REVISED: allow Seville (7) to fly not only to Paris (1) but also directly to Stockholm (4)
    7: [1, 4],
    8: [1, 2, 3, 4, 5, 9],
    9: [1, 3, 5, 6, 8]
}

solver = Solver()

# Create 10 integer variables "order[i]": which city index is visited at slot i.
order = [Int(f"order_{i}") for i in range(10)]
# T[i] represents the starting day when arriving at the city in slot i.
T = [Int(f"T_{i}") for i in range(10)]

# Each order variable must be one of the 10 city indices.
for i in range(10):
    solver.add(And(order[i] >= 0, order[i] < 10))
# All cities are visited exactly once.
solver.add(Distinct(order))

# “Help” the solver with these fixes:
solver.add(order[0] == 3)  # Berlin
solver.add(order[8] == 4)  # Stockholm
solver.add(order[9] == 2)  # Riga

# Helper: given an (expression for a) city index, returns that city’s duration.
def get_duration(city_expr):
    return Sum([If(city_expr == i, durations[i], 0) for i in range(len(durations))])

# The itinerary lasts exactly 23 days.
solver.add(T[0] == 1)
for i in range(9):
    solver.add(T[i+1] == T[i] + (get_duration(order[i]) - 1))
solver.add(T[9] + get_duration(order[9]) - 1 == 23)

# Special event constraints:
# Berlin (city 3) must be visited early (start day <= 2)
for i in range(10):
    solver.add(Implies(order[i] == 3, T[i] <= 2))
# Stockholm (city 4) must start on day 20
for i in range(10):
    solver.add(Implies(order[i] == 4, T[i] == 20))
# Nice (city 6) must start on day 11, 12, or 13
for i in range(10):
    solver.add(Implies(order[i] == 6, Or(T[i] == 11, T[i] == 12, T[i] == 13)))

# Flight connectivity: consecutive cities must be connected by a direct flight.
for i in range(9):
    con_list = []
    for city in range(10):
        neighbors = allowed_neighbors.get(city, [])
        con_list.append(Implies(order[i] == city, Or([order[i+1] == nb for nb in neighbors])))
    solver.add(And(con_list))

# Try to find and print a valid itinerary.
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(10):
        city_index = model.evaluate(order[i]).as_long()
        start_day = model.evaluate(T[i]).as_long()
        duration_val = durations[city_index]
        end_day = start_day + duration_val - 1
        itinerary.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": cities[city_index]
        })
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"itinerary": []}))