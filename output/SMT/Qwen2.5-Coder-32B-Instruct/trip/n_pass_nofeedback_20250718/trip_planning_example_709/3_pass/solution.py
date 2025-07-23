from z3 import *

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

# Define the variables for the start day of each city
start_days = {city: Int(f"start_{city}") for city in cities}

# Add constraints for the start days
for city, duration in cities.items():
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] + duration <= total_days)

# Add constraints for the friend meeting in Porto between day 16 and day 18
solver.add(start_days["Porto"] + cities["Porto"] - 1 >= 16)
solver.add(start_days["Porto"] <= 18)

# Add constraints for the direct flights
for (city1, city2) in flights:
    # If you start city2 after city1, you must fly from city1 to city2
    solver.add(Or(start_days[city2] >= start_days[city1] + cities[city1],
                 start_days[city1] >= start_days[city2] + cities[city2]))

# Ensure that each day is spent in exactly one city
for day in range(1, total_days + 1):
    city_vars = [If(And(start_days[city] <= day, day < start_days[city] + cities[city]), city, "") for city in cities]
    solver.add(Sum([If(city_var != "", 1, 0) for city_var in city_vars]) == 1)

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for day in range(1, total_days + 1):
        for city in cities:
            if model.evaluate(start_days[city] <= day) and model.evaluate(day < start_days[city] + cities[city]):
                itinerary.append({"day": day, "place": city})
                break  # No need to check other cities for this day
    # Convert the itinerary to JSON format
    import json
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found")