from z3 import *
import json

# Define the cities and their respective stay durations
cities = {
    "Reykjavik": 5,
    "Istanbul": 4,
    "Edinburgh": 5,
    "Oslo": 2,
    "Stuttgart": 3,
    "Bucharest": 5
}

# Define the constraints for specific cities
constraints = {
    "Istanbul": (5, 8),  # Meet friends between day 5 and day 8
    "Oslo": (8, 9),     # Visit relatives between day 8 and day 9
}

# Define the direct flights between cities
flights = {
    ("Bucharest", "Oslo"),
    ("Istanbul", "Oslo"),
    ("Reykjavik", "Stuttgart"),
    ("Bucharest", "Istanbul"),
    ("Stuttgart", "Edinburgh"),
    ("Istanbul", "Edinburgh"),
    ("Oslo", "Reykjavik"),
    ("Istanbul", "Stuttgart"),
    ("Oslo", "Edinburgh"),
}

# Create a solver instance
solver = Solver()

# Define variables for the start day of each city
start_days = {city: Int(f"start_{city}") for city in cities}

# Add constraints for the start days
for city, duration in cities.items():
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] + duration <= 19)

# Add constraints for specific cities
solver.add(start_days["Istanbul"] + 4 >= 5)
solver.add(start_days["Istanbul"] <= 8)
solver.add(start_days["Oslo"] + 2 >= 8)
solver.add(start_days["Oslo"] <= 9)

# Add constraints for direct flights
for (city1, city2) in flights:
    # If you start in city1 and end in city2, the end day of city1 must be the start day of city2
    # This means the last day in city1 is also the first day in city2
    solver.add(Or(start_days[city1] + cities[city1] < start_days[city2],
                 start_days[city2] + cities[city2] < start_days[city1],
                 start_days[city1] + cities[city1] == start_days[city2]))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for city in cities:
        start_day = model[start_days[city]].as_long()
        end_day = start_day + cities[city] - 1
        for day in range(start_day, end_day + 1):
            itinerary.append({"day": day, "place": city})
    itinerary.sort(key=lambda x: x["day"])
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found")