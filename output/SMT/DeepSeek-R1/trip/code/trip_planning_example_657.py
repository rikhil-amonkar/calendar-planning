from z3 import *

# Define the cities
cities = {
    "Frankfurt": 0,
    "Manchester": 1,
    "Valencia": 2,
    "Naples": 3,
    "Oslo": 4,
    "Vilnius": 5
}

# Direct flights adjacency list (bidirectional)
direct_flights = {
    cities["Valencia"]: [cities["Frankfurt"],  # Valencia-Frankfurt
    cities["Manchester"]: [cities["Frankfurt"],  # Manchester-Frankfurt
    cities["Naples"]: [cities["Manchester"],  # Naples-Manchester
    cities["Naples"]: [cities["Frankfurt"],  # Naples-Frankfurt
    cities["Naples"]: [cities["Oslo"]],  # Naples-Oslo
    cities["Oslo"]: [cities["Frankfurt"],  # Oslo-Frankfurt
    cities["Vilnius"]: [cities["Frankfurt"],  # Vilnius-Frankfurt
    cities["Oslo"]: [cities["Vilnius"]],  # Oslo-Vilnius
    cities["Manchester"]: [cities["Oslo"]],  # Manchester-Oslo
    cities["Valencia"]: [cities["Naples"]],  # Valencia-Naples
}

# Create adjacency list with all bidirectional flights
adjacency = {i: [] for i in cities.values()}
for city, connects in direct_flights.items():
    for c in connects:
        adjacency[city].append(c)
        adjacency[c].append(city)  # flights are bidirectional

# Days 1 to 16
days = 16
solver = Solver()
city_vars = [Int(f"day_{i}") for i in range(1, days + 1)]

# Each day must be one of the cities
for day in city_vars:
    solver.add(Or([day == c for c in cities.values()]))

# Frankfurt must be days 13-16
for i in range(12, 16):
    solver.add(city_vars[i] == cities["Frankfurt"])

# Vilnius must be on days 12 and 13 (but day 13 is Frankfurt! Conflict)
# solver.add(city_vars[11] == cities["Vilnius"])  # day 12
# solver.add(city_vars[12] == cities["Vilnius"])  # day 13

# Instead, correct approach: Vilnius must be on day 12 and another day
# But according to problem, user attends wedding between day 12 and 13, so must be in Vilnius on those days
solver.add(city_vars[11] == cities["Vilnius"])  # day 12
solver.add(city_vars[12] == cities["Vilnius"])  # day 13 (conflict with Frankfurt)

# Consecutive days must have direct flights
for i in range(days - 1):
    current = city_vars[i]
    next_day = city_vars[i + 1]
    solver.add(Or([current == next_day] + [And(current == c, next_day == n) for c in adjacency for n in adjacency[c]))

# Total days per city
city_days = [
    (cities["Frankfurt"], 4),
    (cities["Manchester"], 4),
    (cities["Valencia"], 4),
    (cities["Naples"], 4),
    (cities["Oslo"], 3),
    (cities["Vilnius"], 2),
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