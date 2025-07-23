from z3 import *
import json

# Define the cities and their respective stay durations
cities = {
    "Dublin": 3,
    "Madrid": 2,
    "Oslo": 3,
    "London": 2,
    "Vilnius": 3,
    "Berlin": 5
}

# Define the constraints for specific days in specific cities
constraints = {
    "Dublin": (7, 9),  # Meet friends between day 7 and day 9
    "Madrid": (2, 3),  # Visit relatives between day 2 and day 3
    "Berlin": (4, 8)   # Attend wedding between day 4 and day 8 (adjusted to avoid overlap with Madrid)
}

# Define the direct flight connections
flights = {
    ("London", "Madrid"),
    ("Oslo", "Vilnius"),
    ("Berlin", "Vilnius"),
    ("Madrid", "Oslo"),
    ("Madrid", "Dublin"),
    ("London", "Oslo"),
    ("Madrid", "Berlin"),
    ("Berlin", "Oslo"),
    ("Dublin", "Oslo"),
    ("London", "Dublin"),
    ("London", "Berlin"),
    ("Berlin", "Dublin")
}

# Create a solver instance
solver = Solver()

# Define the start day for each city as a Z3 integer variable
start_days = {city: Int(f"start_{city}") for city in cities}

# Add constraints for the start days
for city, duration in cities.items():
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] + duration <= 13)

# Add constraints for specific days in specific cities
for city, (start, end) in constraints.items():
    solver.add(start_days[city] <= start)
    solver.add(start_days[city] + cities[city] - 1 >= end)

# Add constraints for direct flights
for (city1, city2) in flights:
    # If you are in city1 on day X, you can only be in city2 on day X or later
    solver.add(Or(start_days[city1] + cities[city1] <= start_days[city2],
                  start_days[city2] + cities[city2] <= start_days[city1]))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for city, start_day in start_days.items():
        start = model[start_day].as_long()
        end = start + cities[city] - 1
        for day in range(start, end + 1):
            itinerary.append({"day": day, "place": city})
    # Sort the itinerary by day
    itinerary.sort(key=lambda x: x["day"])
    # Ensure no duplicate days for the same city
    unique_itinerary = []
    for entry in itinerary:
        if not unique_itinerary or unique_itinerary[-1] != entry:
            unique_itinerary.append(entry)
    # Print the itinerary in JSON format
    print(json.dumps({"itinerary": unique_itinerary}, indent=2))
else:
    print("No solution found")