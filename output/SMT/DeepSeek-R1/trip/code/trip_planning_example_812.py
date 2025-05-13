from z3 import *

# Define the cities
cities = {
    "Paris": 0,
    "Florence": 1,
    "Vienna": 2,
    "Porto": 3,
    "Munich": 4,
    "Nice": 5,
    "Warsaw": 6
}

# Direct flights adjacency list (bidirectional as per problem description)
adjacency = {
    cities["Paris"]: [cities["Warsaw"], cities["Florence"], cities["Vienna"], cities["Nice"], cities["Munich"], cities["Porto"]],
    cities["Florence"]: [cities["Vienna"], cities["Munich"], cities["Paris"]],
    cities["Vienna"]: [cities["Florence"], cities["Munich"], cities["Porto"], cities["Warsaw"], cities["Paris"], cities["Nice"]],
    cities["Porto"]: [cities["Vienna"], cities["Munich"], cities["Nice"], cities["Paris"], cities["Warsaw"]],
    cities["Munich"]: [cities["Vienna"], cities["Warsaw"], cities["Nice"], cities["Porto"], cities["Paris"]],
    cities["Nice"]: [cities["Munich"], cities["Warsaw"], cities["Porto"], cities["Vienna"], cities["Paris"]],
    cities["Warsaw"]: [cities["Paris"], cities["Vienna"], cities["Munich"], cities["Nice"], cities["Porto"]],
}

# Days 1 to 20
days = 20
solver = Solver()
city_vars = [Int(f"day_{i}") for i in range(1, days + 1)]

# Each day must be one of the cities
for day in city_vars:
    solver.add(Or([day == c for c in cities.values()]))

# Porto must be days 1-3 (workshop)
solver.add(city_vars[0] == cities["Porto"])  # Day 1
solver.add(city_vars[1] == cities["Porto"])  # Day 2
solver.add(city_vars[2] == cities["Porto"])  # Day 3

# Warsaw must be days 13-15 (wedding)
solver.add(city_vars[12] == cities["Warsaw"])  # Day 13
solver.add(city_vars[13] == cities["Warsaw"])  # Day 14
solver.add(city_vars[14] == cities["Warsaw"])  # Day 15

# Vienna must be days 19-20 (relatives)
solver.add(city_vars[18] == cities["Vienna"])  # Day 19
solver.add(city_vars[19] == cities["Vienna"])  # Day 20

# Consecutive days must have direct flights
for i in range(days - 1):
    current = city_vars[i]
    next_day = city_vars[i + 1]
    solver.add(Or([current == next_day] + [And(current == c, next_day == n) for c in adjacency for n in adjacency[c]))

# Total days per city
city_days = [
    (cities["Paris"], 5),
    (cities["Florence"], 3),
    (cities["Vienna"], 2),
    (cities["Porto"], 3),
    (cities["Munich"], 5),
    (cities["Nice"], 5),
    (cities["Warsaw"], 3),
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