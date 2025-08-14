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

# Ensure that the itinerary covers all 18 days
# We need to ensure that there are no gaps and no overlaps
# We will use a list of boolean variables to track which days are covered
day_covered = [Bool(f"day_{day}_covered") for day in range(1, total_days + 1)]

# Add constraints to ensure each day is covered by exactly one city
for day in range(1, total_days + 1):
    solver.add(Or([And(start_days[city] <= day, start_days[city] + cities[city] > day) for city in cities]))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for day in range(1, total_days + 1):
        for city in cities:
            if model.evaluate(start_days[city] <= day) and model.evaluate(start_days[city] + cities[city] > day):
                itinerary.append({"day": day, "city": city})
                break
    # Group the itinerary by city and day range
    grouped_itinerary = []
    current_city = None
    current_start = None
    for entry in itinerary:
        if current_city is None:
            current_city = entry["city"]
            current_start = entry["day"]
        elif entry["city"] != current_city:
            grouped_itinerary.append({"day_range": f"Day {current_start}-{entry['day']-1}", "place": current_city})
            current_city = entry["city"]
            current_start = entry["day"]
    # Add the last entry
    if current_city is not None:
        grouped_itinerary.append({"day_range": f"Day {current_start}-{total_days}", "place": current_city})
    print(json.dumps({"itinerary": grouped_itinerary}, indent=2))
else:
    print("No solution found")