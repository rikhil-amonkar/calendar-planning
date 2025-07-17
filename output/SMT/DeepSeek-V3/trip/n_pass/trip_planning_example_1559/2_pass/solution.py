import json
from z3 import *

# Define the cities and their required days
cities = {
    "Valencia": 2,
    "Oslo": 3,
    "Lyon": 4,
    "Prague": 3,
    "Paris": 4,
    "Nice": 4,
    "Seville": 5,
    "Tallinn": 2,
    "Mykonos": 5,
    "Lisbon": 2
}

# Define the direct flights as a set of tuples
direct_flights = [
    ("Lisbon", "Paris"),
    ("Lyon", "Nice"),
    ("Tallinn", "Oslo"),
    ("Prague", "Lyon"),
    ("Paris", "Oslo"),
    ("Lisbon", "Seville"),
    ("Prague", "Lisbon"),
    ("Oslo", "Nice"),
    ("Valencia", "Paris"),
    ("Valencia", "Lisbon"),
    ("Paris", "Nice"),
    ("Nice", "Mykonos"),
    ("Paris", "Lyon"),
    ("Valencia", "Lyon"),
    ("Prague", "Oslo"),
    ("Prague", "Paris"),
    ("Seville", "Paris"),
    ("Oslo", "Lyon"),
    ("Prague", "Valencia"),
    ("Lisbon", "Nice"),
    ("Lisbon", "Oslo"),
    ("Valencia", "Seville"),
    ("Lisbon", "Lyon"),
    ("Paris", "Tallinn"),
    ("Prague", "Tallinn")
]

# Make sure the flights are bidirectional
bidirectional_flights = set()
for a, b in direct_flights:
    bidirectional_flights.add((a, b))
    bidirectional_flights.add((b, a))

# Initialize Z3 solver
solver = Solver()

# Create variables for each day (1 to 25)
days = [Int(f"day_{i}") for i in range(1, 26)]

# Define the city names as integers
city_names = {city: idx for idx, city in enumerate(cities.keys())}
city_indices = {idx: city for idx, city in enumerate(cities.keys())}

# Add constraints that each day's variable is within the city indices
for day in days:
    solver.add(day >= 0, day < len(cities))

# Constraint: Total days per city must match the required days
for city, required_days in cities.items():
    solver.add(Sum([If(day == city_names[city], 1, 0) for day in days]) == required_days)

# Specific constraints:
# Valencia for 2 days, meet friends between day 3 and 4 (i.e., must be in Valencia on day 3 or 4)
solver.add(Or(days[2] == city_names["Valencia"], days[3] == city_names["Valencia"]))  # days are 1-based

# Oslo for 3 days, meet friend between day 13 and 15 (i.e., must be in Oslo on at least one of days 13, 14, or 15)
solver.add(Or([days[i] == city_names["Oslo"] for i in range(12, 15)]))  # days 13-15 (1-based)

# Seville: annual show from day 5 to day 9 (must be in Seville during these days)
for i in range(4, 9):  # days 5-9 (1-based)
    solver.add(days[i] == city_names["Seville"])

# Mykonos: wedding between day 21 and 25 (must be in Mykonos during these days)
for i in range(20, 25):  # days 21-25 (1-based)
    solver.add(days[i] == city_names["Mykonos"])

# Flight constraints: consecutive days must be the same city or have a direct flight
for i in range(24):
    current = days[i]
    next_c = days[i+1]
    # Either stay in the same city or use a direct flight
    same_city = current == next_c
    flight_exists = Or([And(current == city_names[a], next_c == city_names[b]) for a, b in bidirectional_flights])
    solver.add(Or(same_city, flight_exists))

# Check if the solver is satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(1, 26):
        city_idx = model.evaluate(days[i-1]).as_long()
        city = city_indices[city_idx]
        itinerary.append({"day": i, "place": city})
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No valid itinerary found.")