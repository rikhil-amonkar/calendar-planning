from z3 import *
import json

# Define the cities and their respective stay durations
cities = {
    "Oslo": 2,
    "Helsinki": 2,
    "Edinburgh": 3,
    "Riga": 2,
    "Tallinn": 5,
    "Budapest": 5,
    "Vilnius": 5,
    "Porto": 5,
    "Geneva": 4
}

# Define the constraints for specific days
constraints = {
    "Oslo": (24, 25),
    "Tallinn": (4, 8)
}

# Define the direct flights between cities
flights = {
    ("Porto", "Oslo"), ("Edinburgh", "Budapest"), ("Edinburgh", "Geneva"),
    ("Riga", "Tallinn"), ("Edinburgh", "Porto"), ("Vilnius", "Helsinki"),
    ("Tallinn", "Vilnius"), ("Riga", "Oslo"), ("Geneva", "Oslo"),
    ("Edinburgh", "Oslo"), ("Edinburgh", "Helsinki"), ("Vilnius", "Oslo"),
    ("Riga", "Helsinki"), ("Budapest", "Geneva"), ("Helsinki", "Budapest"),
    ("Helsinki", "Oslo"), ("Edinburgh", "Riga"), ("Tallinn", "Helsinki"),
    ("Geneva", "Porto"), ("Budapest", "Oslo"), ("Helsinki", "Geneva"),
    ("Riga", "Vilnius"), ("Tallinn", "Oslo")
}

# Create a solver instance
solver = Solver()

# Define the city visited on each day as a Z3 string variable
day_to_city = [String(f"day_{i}") for i in range(1, 26)]

# Add constraints for each city's stay duration
for city, duration in cities.items():
    # Find the start day for the city
    start_day = Int(f"start_{city}")
    solver.add(start_day >= 1)
    solver.add(start_day + duration - 1 <= 25)
    # Ensure the city is visited for the correct duration
    for day in range(1, 26):
        solver.add(Or(day_to_city[day-1] != city, start_day <= day, day <= start_day + duration - 1))

# Add constraints for specific days
for city, (start, end) in constraints.items():
    # Find the start day for the city
    start_day = Int(f"start_{city}")
    solver.add(start_day + cities[city] - 1 >= start)
    solver.add(start_day <= end)

# Add constraints for direct flights
for (city1, city2) in flights:
    # Find the start day for the cities
    start_day1 = Int(f"start_{city1}")
    start_day2 = Int(f"start_{city2}")
    # Ensure the transition is valid
    solver.add(Or(start_day2 != start_day1 + cities[city1],
                 start_day2 == start_day1 + cities[city1]))

# Add constraints to ensure each city is visited only once
for city in cities:
    solver.add(Sum([If(day_to_city[day-1] == city, 1, 0) for day in range(1, 26)]) == 1)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for day in range(1, 26):
        city = model[day_to_city[day-1]].as_string()[1:-1]  # Remove quotes from the string
        itinerary.append({"day": day, "city": city})
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found")