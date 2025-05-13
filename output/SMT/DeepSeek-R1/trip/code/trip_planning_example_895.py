from z3 import *

# Define the cities
cities = {
    "Brussels": 0,
    "Venice": 1,
    "London": 2,
    "Lisbon": 3,
    "Reykjavik": 4,
    "Santorini": 5,
    "Madrid": 6
}

# Direct flights adjacency list (bidirectional)
adjacency = {
    cities["Brussels"]: [cities["Venice"], cities["London"], cities["Lisbon"], cities["Reykjavik"], cities["Madrid"]],
    cities["Venice"]: [cities["Brussels"], cities["Madrid"], cities["Santorini"], cities["Lisbon"], cities["London"]],
    cities["London"]: [cities["Brussels"], cities["Madrid"], cities["Santorini"], cities["Reykjavik"], cities["Lisbon"], cities["Venice"]],
    cities["Lisbon"]: [cities["Reykjavik"], cities["Venice"], cities["London"], cities["Madrid"], cities["Brussels"]],
    cities["Reykjavik"]: [cities["Lisbon"], cities["Madrid"], cities["London"], cities["Brussels"]],
    cities["Santorini"]: [cities["Venice"], cities["Madrid"], cities["London"]],
    cities["Madrid"]: [cities["Venice"], cities["Reykjavik"], cities["London"], cities["Santorini"], cities["Lisbon"], cities["Brussels"]]
}

# Days 1 to 17
days = 17
solver = Solver()
city_vars = [Int(f"day_{i}") for i in range(1, days + 1)]

# Each day must be one of the cities
for day in city_vars:
    solver.add(Or([day == c for c in cities.values()]))

# Brussels must be days 1-2 (conference)
solver.add(city_vars[0] == cities["Brussels"])  # Day 1
solver.add(city_vars[1] == cities["Brussels"])  # Day 2

# Venice must be days 5-7 (relatives)
solver.add(city_vars[4] == cities["Venice"])  # Day 5
solver.add(city_vars[5] == cities["Venice"])  # Day 6
solver.add(city_vars[6] == cities["Venice"])  # Day 7

# Madrid must be days 7-11 (wedding)
solver.add(city_vars[6] == cities["Madrid"])  # Day 7 (Conflict)
solver.add(city_vars[7] == cities["Madrid"])  # Day 8
solver.add(city_vars[8] == cities["Madrid"])  # Day 9
solver.add(city_vars[9] == cities["Madrid"])  # Day 10
solver.add(city_vars[10] == cities["Madrid"])  # Day 11

# Consecutive days must have direct flights
for i in range(days - 1):
    current = city_vars[i]
    next_day = city_vars[i + 1]
    solver.add(Or([current == next_day] + [And(current == c, next_day == n) for c in adjacency for n in adjacency[c]))

# Total days per city
city_days = [
    (cities["Brussels"], 2),
    (cities["Venice"], 3),
    (cities["London"], 3),
    (cities["Lisbon"], 4),
    (cities["Reykjavik"], 3),
    (cities["Santorini"], 3),
    (cities["Madrid"], 5),
]

for city, total in city_days:
    solver.add(Sum([If(city_var == city, 1, 0) for city_var in city_vars]) == total)

# Check and print solution
if solver.check() == sat:
    model = solver.model()
    schedule = [model[day].as_long() for day in city_vars]
    inv_cities = {v: k for k, v in cities.items()}
    for i in range(days):
        print(f"Day {i + 1}: {inv_cities[schedule[i]]}")
else:
    print("No valid schedule exists.")