from z3 import *
import json

# Define the solver
solver = Solver()

# Define the number of days
total_days = 20

# Define the cities and their required stay durations
cities = {
    "Hamburg": 7,
    "Munich": 6,
    "Manchester": 2,
    "Lyon": 2,
    "Split": 7
}

# Define the constraints for specific days
specific_days = {
    "Manchester": (19, 20),  # Visit relatives
    "Lyon": (13, 14)        # Annual show
}

# Define the direct flights between cities
flights = {
    ("Split", "Munich"),
    ("Munich", "Manchester"),
    ("Hamburg", "Manchester"),
    ("Hamburg", "Munich"),
    ("Split", "Lyon"),
    ("Lyon", "Munich"),
    ("Hamburg", "Split"),
    ("Manchester", "Split")
}

# Create variables for the start day of each city
start_days = {city: Int(f"start_{city}") for city in cities}

# Add constraints for the start days
for city, days in cities.items():
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] + days <= total_days)

# Add constraints for specific days
solver.add(start_days["Manchester"] + cities["Manchester"] - 1 >= specific_days["Manchester"][0])
solver.add(start_days["Manchester"] <= specific_days["Manchester"][1])
solver.add(start_days["Lyon"] + cities["Lyon"] - 1 >= specific_days["Lyon"][0])
solver.add(start_days["Lyon"] <= specific_days["Lyon"][1])

# Add constraints for direct flights
for i in range(total_days):
    for city1 in cities:
        for city2 in cities:
            if city1 != city2 and (city1, city2) not in flights and (city2, city1) not in flights:
                # If city1 is on day i+1, then city2 cannot be on day i+1
                solver.add(Or(start_days[city1] + cities[city1] <= i + 1, start_days[city2] >= i + 2))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    print("Model found:")
    for city, start in start_days.items():
        print(f"{city}: Start day {model.evaluate(start)}")
    
    itinerary = []
    for day in range(1, total_days + 1):
        for city, start in start_days.items():
            if model.evaluate(start) <= day and model.evaluate(start) + cities[city] >= day:
                itinerary.append({"day": day, "city": city})
                break
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found")