from z3 import *

# Define the cities
cities = {
    "Vienna": 0,
    "Milan": 1,
    "Rome": 2,
    "Riga": 3,
    "Lisbon": 4,
    "Vilnius": 5,
    "Oslo": 6
}

# Direct flights adjacency list (bidirectional)
adjacency = {
    cities["Vienna"]: [cities["Milan"], cities["Vilnius"], cities["Lisbon"], cities["Riga"], cities["Rome"], cities["Oslo"]],
    cities["Milan"]: [cities["Vienna"], cities["Riga"], cities["Oslo"], cities["Vilnius"], cities["Lisbon"]],
    cities["Rome"]: [cities["Oslo"], cities["Riga"], cities["Lisbon"], cities["Vienna"]],
    cities["Riga"]: [cities["Oslo"], cities["Milan"], cities["Rome"], cities["Vilnius"], cities["Lisbon"], cities["Vienna"]],
    cities["Lisbon"]: [cities["Vienna"], cities["Oslo"], cities["Rome"], cities["Riga"], cities["Milan"]],
    cities["Vilnius"]: [cities["Vienna"], cities["Oslo"], cities["Milan"], cities["Riga"]],
    cities["Oslo"]: [cities["Riga"], cities["Rome"], cities["Vienna"], cities["Milan"], cities["Vilnius"], cities["Lisbon"]]
}

# Days 1 to 15
days = 15
solver = Solver()
city_vars = [Int(f"day_{i}") for i in range(1, days + 1)]

# Each day must be one of the cities
for day in city_vars:
    solver.add(Or([day == c for c in cities.values()]))

# Vienna must be days 1-4 (conference)
for i in range(4):
    solver.add(city_vars[i] == cities["Vienna"])

# Lisbon must be days 11-13 (relatives)
solver.add(city_vars[10] == cities["Lisbon"])  # Day 11
solver.add(city_vars[11] == cities["Lisbon"])  # Day 12
solver.add(city_vars[12] == cities["Lisbon"])  # Day 13

# Oslo must be days 13-15 (friend)
solver.add(city_vars[12] == cities["Oslo"])   # Day 13
solver.add(city_vars[13] == cities["Oslo"])   # Day 14
solver.add(city_vars[14] == cities["Oslo"])   # Day 15

# Consecutive days must have direct flights
for i in range(days - 1):
    current = city_vars[i]
    next_day = city_vars[i + 1]
    solver.add(Or([current == next_day] + [And(current == c, next_day == n) for c in adjacency for n in adjacency[c]))

# Total days per city
city_days = [
    (cities["Vienna"], 4),
    (cities["Milan"], 2),
    (cities["Rome"], 3),
    (cities["Riga"], 2),
    (cities["Lisbon"], 3),
    (cities["Vilnius"], 4),
    (cities["Oslo"], 3),
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