from z3 import *
import json

# Define the cities and their respective stay durations
cities = {
    "Stuttgart": 4,
    "Istanbul": 4,
    "Vilnius": 4,
    "Seville": 3,
    "Geneva": 5,
    "Valencia": 5,
    "Munich": 3,
    "Reykjavik": 4
}

# Define the constraints for specific days
constraints = {
    "Stuttgart": [(4, 7)],  # Conference days
    "Istanbul": [(19, 22)],  # Visit relatives days
    "Munich": [(13, 15)],  # Annual show days
    "Reykjavik": [(1, 4)]   # Workshop days
}

# Define the direct flight connections
flights = {
    "Geneva": ["Istanbul"],
    "Reykjavik": ["Munich", "Stuttgart"],
    "Stuttgart": ["Valencia", "Istanbul"],
    "Munich": ["Geneva", "Istanbul", "Vilnius", "Seville", "Valencia"],
    "Istanbul": ["Vilnius", "Valencia", "Munich"],
    "Vilnius": ["Munich"],
    "Valencia": ["Seville", "Istanbul", "Geneva", "Munich"],
    "Seville": ["Munich"],
    "Munich": ["Geneva", "Istanbul", "Vilnius", "Seville", "Valencia"]
}

# Create a solver instance
solver = Solver()

# Define the start day for each city as a Z3 integer variable
start_days = {city: Int(f"start_{city}") for city in cities}

# Add constraints for the start days
for city, duration in cities.items():
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] + duration <= 25)

# Add constraints for specific days
for city, day_ranges in constraints.items():
    for start, end in day_ranges:
        solver.add(Or([And(start_days[city] <= day, start_days[city] + cities[city] > day) for day in range(start, end + 1)]))

# Add constraints for direct flights
for city, duration in cities.items():
    for other_city in flights[city]:
        if other_city in start_days:
            solver.add(Or(start_days[city] + duration <= start_days[other_city],
                           start_days[other_city] + cities[other_city] <= start_days[city]))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for city, start in start_days.items():
        start_day = model.evaluate(start).as_long()
        itinerary.append((start_day, city))
    itinerary.sort()
    day_place_mapping = []
    for i in range(1, 26):
        for start_day, city in itinerary:
            if start_day <= i < start_day + cities[city]:
                day_place_mapping.append({"day": i, "place": city})
                break
    print(json.dumps({"itinerary": day_place_mapping}, indent=2))
else:
    print("No solution found")