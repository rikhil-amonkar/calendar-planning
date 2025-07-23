from z3 import *
import json

# Define the solver
solver = Solver()

# Define the number of days
num_days = 14

# Define the cities
cities = ["Helsinki", "Warsaw", "Madrid", "Split", "Reykjavik", "Budapest"]

# Define the variables for the start day in each city
start_days = {city: Int(f"start_{city}") for city in cities}

# Define the duration for each city
durations = {
    "Helsinki": 2,
    "Warsaw": 3,
    "Madrid": 4,
    "Split": 4,
    "Reykjavik": 2,
    "Budapest": 4
}

# Add constraints for the duration of stay in each city
for city, duration in durations.items():
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] + duration - 1 <= num_days)

# Add constraints for specific days in specific cities
solver.add(Or(start_days["Helsinki"] == 1, start_days["Helsinki"] == 2))
solver.add(Or(start_days["Warsaw"] == 9, start_days["Warsaw"] == 10, start_days["Warsaw"] == 11))
solver.add(Or(start_days["Reykjavik"] == 8, start_days["Reykjavik"] == 9))

# Define the direct flight connections
connections = [
    ("Helsinki", "Reykjavik"),
    ("Budapest", "Warsaw"),
    ("Madrid", "Split"),
    ("Helsinki", "Split"),
    ("Helsinki", "Madrid"),
    ("Helsinki", "Budapest"),
    ("Reykjavik", "Warsaw"),
    ("Helsinki", "Warsaw"),
    ("Madrid", "Budapest"),
    ("Budapest", "Reykjavik"),
    ("Madrid", "Warsaw"),
    ("Warsaw", "Split"),
    ("Reykjavik", "Madrid")
]

# Add constraints for transitions between cities
for i in range(1, num_days + 1):
    for city1 in cities:
        for city2 in cities:
            if city1 != city2:
                # If you are in city1 on day i, you must be in city1 or city2 on day i+1 if there is a direct flight
                if (city1, city2) in connections or (city2, city1) in connections:
                    solver.add(Or(
                        Or([start_days[city1] + j != i for j in range(durations[city1])]),
                        Or([start_days[city2] + j != i + 1 for j in range(durations[city2])])
                    ))

# Ensure that each day is covered by exactly one city
for day in range(1, num_days + 1):
    solver.add(Or([And(start_days[city] <= day, start_days[city] + durations[city] - 1 >= day) for city in cities]))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for day in range(1, num_days + 1):
        for city in cities:
            if model.evaluate(start_days[city] <= day) and model.evaluate(start_days[city] + durations[city] - 1 >= day):
                itinerary.append({"day": day, "city": city})
                break
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found")