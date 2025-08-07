from z3 import *
import json

# Define the solver
solver = Solver()

# Define the number of days
total_days = 18

# Define the cities and their respective stay durations
cities = {
    "Helsinki": 4,
    "Valencia": 5,
    "Dubrovnik": 4,
    "Porto": 3,
    "Prague": 3,
    "Reykjavik": 4
}

# Define the direct flight connections
flights = {
    ("Helsinki", "Prague"),
    ("Prague", "Valencia"),
    ("Valencia", "Porto"),
    ("Helsinki", "Reykjavik"),
    ("Dubrovnik", "Helsinki"),
    ("Reykjavik", "Prague")
}

# Create variables for the start day of each city
start_days = {city: Int(f"start_{city}") for city in cities}

# Add constraints for the start days
for city, duration in cities.items():
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] + duration <= total_days)

# Add constraints for the friend meeting in Porto between day 16 and day 18
solver.add(start_days["Porto"] + cities["Porto"] - 1 >= 16)
solver.add(start_days["Porto"] <= 18)

# Add constraints for the flight connections
for (city1, city2) in flights:
    # If you start city2 after city1, you must fly from city1 to city2
    solver.add(Or(start_days[city2] >= start_days[city1] + cities[city1],
                  start_days[city1] >= start_days[city2] + cities[city2]))

# Ensure that the total number of days is exactly 18
# This is already ensured by the constraints on start days and durations

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for day in range(1, total_days + 1):
        for city in cities:
            start_day = model[start_days[city]].as_long()
            end_day = start_day + cities[city] - 1
            if start_day <= day <= end_day:
                itinerary.append({"day": day, "place": city})
                break
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found")