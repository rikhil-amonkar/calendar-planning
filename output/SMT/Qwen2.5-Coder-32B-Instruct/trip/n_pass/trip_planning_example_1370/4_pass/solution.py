from z3 import *
import json

# Define the cities and their respective stay durations
cities = {
    "Santorini": 5,
    "Krakow": 5,
    "Paris": 5,
    "Vilnius": 3,
    "Munich": 5,
    "Geneva": 2,
    "Amsterdam": 4,
    "Budapest": 5,
    "Split": 4
}

# Define the direct flight connections
flights = {
    ("Paris", "Krakow"), ("Paris", "Amsterdam"), ("Paris", "Split"),
    ("Vilnius", "Munich"), ("Paris", "Geneva"), ("Amsterdam", "Geneva"),
    ("Munich", "Split"), ("Split", "Krakow"), ("Munich", "Amsterdam"),
    ("Budapest", "Amsterdam"), ("Split", "Amsterdam"), ("Santorini", "Geneva"),
    ("Amsterdam", "Santorini"), ("Munich", "Budapest"), ("Munich", "Paris"),
    ("Krakow", "Vilnius"), ("Vilnius", "Amsterdam"), ("Budapest", "Paris"),
    ("Krakow", "Amsterdam"), ("Vilnius", "Paris"), ("Budapest", "Geneva"),
    ("Split", "Amsterdam"), ("Vilnius", "Split"), ("Munich", "Geneva"),
    ("Munich", "Krakow")
}

# Create a solver instance
solver = Solver()

# Define the start day for each city as a Z3 integer variable
start_days = {city: Int(f"start_{city}") for city in cities}

# Add constraints for the start days
for city, duration in cities.items():
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] + duration <= 30)

# Add constraints for the specific days in certain cities
solver.add(start_days["Santorini"] + 4 >= 25)  # Santorini: day 25-29
solver.add(start_days["Santorini"] <= 25)
solver.add(start_days["Krakow"] + 4 >= 18)    # Krakow: day 18-22
solver.add(start_days["Krakow"] <= 18)
solver.add(start_days["Paris"] + 4 >= 11)     # Paris: day 11-15
solver.add(start_days["Paris"] <= 11)

# Add constraints for transitions between cities
for (city1, city2) in flights:
    # If you start in city1 and end in city2, the start day of city2 must be the end day of city1
    # This means the start day of city2 must be the start day of city1 plus the duration of city1
    solver.add(Or(start_days[city2] >= start_days[city1] + cities[city1],
                  start_days[city1] >= start_days[city2] + cities[city2]))

# Ensure that the total duration of the stay in all cities is exactly 30 days
# This means that the last day of the last city must be 30
last_day = Int("last_day")
solver.add(last_day == 30)

# Add constraints to ensure that the last day of the last city is covered
for city, duration in cities.items():
    solver.add(last_day >= start_days[city] + duration - 1)

# Ensure that the itinerary covers exactly 30 days
# We need to ensure that there are no gaps and the total duration is exactly 30 days
# We will use a list of boolean variables to track which days are covered
covered_days = [Bool(f"day_{day}") for day in range(1, 31)]

# Add constraints to ensure each day is covered by exactly one city
for day in range(1, 31):
    day_covered = Or([And(start_days[city] <= day, start_days[city] + cities[city] > day) for city in cities])
    solver.add(day_covered)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for day in range(1, 31):
        for city in cities:
            start_day = model[start_days[city]].as_long()
            end_day = start_day + cities[city] - 1
            if start_day <= day <= end_day:
                itinerary.append({"day": day, "place": city})
                break
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found")