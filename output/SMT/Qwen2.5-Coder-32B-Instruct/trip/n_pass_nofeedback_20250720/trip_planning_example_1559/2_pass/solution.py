from z3 import *
import json

# Define the solver
solver = Solver()

# Define the cities and their respective stay durations
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

# Define the start day variables for each city
start_days = {city: Int(f"start_{city}") for city in cities}

# Define the constraints
# Each city must be visited within the 25-day period
for city, duration in cities.items():
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] + duration <= 25)

# Specific constraints for each city
# Valencia: 2 days, meet friends between day 3 and day 4
solver.add(start_days["Valencia"] <= 3)
solver.add(start_days["Valencia"] + cities["Valencia"] - 1 >= 4)

# Oslo: 3 days, meet friend between day 13 and day 15
solver.add(start_days["Oslo"] <= 13)
solver.add(start_days["Oslo"] + cities["Oslo"] - 1 >= 15)

# Seville: 5 days, attend show from day 5 to day 9
solver.add(start_days["Seville"] <= 5)
solver.add(start_days["Seville"] + cities["Seville"] - 1 >= 9)

# Mykonos: 5 days, attend wedding between day 21 and day 25
solver.add(start_days["Mykonos"] <= 21)
solver.add(start_days["Mykonos"] + cities["Mykonos"] - 1 >= 25)

# Direct flight constraints
# We need to ensure that the transition between cities is possible via direct flights
direct_flights = [
    ("Lisbon", "Paris"), ("Lyon", "Nice"), ("Tallinn", "Oslo"), ("Prague", "Lyon"),
    ("Paris", "Oslo"), ("Lisbon", "Seville"), ("Prague", "Lisbon"), ("Oslo", "Nice"),
    ("Valencia", "Paris"), ("Valencia", "Lisbon"), ("Paris", "Nice"), ("Nice", "Mykonos"),
    ("Paris", "Lyon"), ("Valencia", "Lyon"), ("Prague", "Oslo"), ("Prague", "Paris"),
    ("Seville", "Paris"), ("Oslo", "Lyon"), ("Prague", "Valencia"), ("Lisbon", "Nice"),
    ("Lisbon", "Oslo"), ("Valencia", "Seville"), ("Lisbon", "Lyon"), ("Paris", "Tallinn"),
    ("Prague", "Tallinn")
]

# Add constraints for all possible direct flights
# Ensure that the transition between cities is valid
for city1 in cities:
    for city2 in cities:
        if city1 != city2 and (city1, city2) in direct_flights:
            solver.add(Or(start_days[city2] == start_days[city1] + cities[city1],
                           start_days[city1] == start_days[city2] + cities[city2]))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for city, duration in cities.items():
        start_day = model[start_days[city]].as_long()
        for day in range(start_day, start_day + duration):
            itinerary.append({"day": day, "city": city})
    itinerary.sort(key=lambda x: x["day"])
    print(json.dumps({"itinerary": itinerary}, indent=4))
else:
    print("No solution found")