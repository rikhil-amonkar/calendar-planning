from z3 import *

# Define the cities
cities = {
    "Madrid": 0,
    "Dublin": 1,
    "Tallinn": 2
}

# Direct flights adjacency list (bidirectional)
direct_flights = {
    cities["Madrid"]: [cities["Dublin"]],
    cities["Dublin"]: [cities["Madrid"], cities["Tallinn"]],
    cities["Tallinn"]: [cities["Dublin"]]
}

# Create adjacency list with all bidirectional flights
adjacency = {i: [] for i in cities.values()}
for city, connects in direct_flights.items():
    adjacency[city] = connects.copy()
    for c in connects:
        if city not in adjacency[c]:
            adjacency[c].append(city)

# Days 1 to 7
days = 7
solver = Solver()
city_vars = [Int(f"day_{i}") for i in range(1, days + 1)]

# Each day must be one of the cities
for day in city_vars:
    solver.add(Or([day == c for c in cities.values()]))

# Tallinn must be days 6 and 7 (workshop)
solver.add(city_vars[5] == cities["Tallinn"])  # Day 6
solver.add(city_vars[6] == cities["Tallinn"])  # Day 7

# Consecutive days must have direct flights
for i in range(days - 1):
    current = city_vars[i]
    next_day = city_vars[i + 1]
    solver.add(Or([current == next_day] + [And(current == c, next_day == n) for c in adjacency for n in adjacency[c]))

# Total days per city
city_days = [
    (cities["Madrid"], 4),
    (cities["Dublin"], 3),
    (cities["Tallinn"], 2),
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