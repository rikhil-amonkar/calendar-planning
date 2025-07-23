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

# Define the days you want to be in specific cities
friends_in_dublin = (7, 9)
relatives_in_madrid = (2, 3)
wedding_in_berlin = (3, 7)

# Define the total number of days
total_days = 13

# Create a solver instance
solver = Solver()

# Define variables for the start day of each city
start_days = {city: Int(f"start_{city}") for city in cities}

# Add constraints for the start days
for city, duration in cities.items():
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] + duration <= total_days)

# Add constraints for specific days in specific cities
solver.add(Or([And(start_days["Dublin"] + i == day) for i, day in enumerate(range(friends_in_dublin[0], friends_in_dublin[1] + 1))]))
solver.add(Or([And(start_days["Madrid"] + i == day) for i, day in enumerate(range(relatives_in_madrid[0], relatives_in_madrid[1] + 1))]))
solver.add(Or([And(start_days["Berlin"] + i == day) for i, day in enumerate(range(wedding_in_berlin[0], wedding_in_berlin[1] + 1))]))

# Define the direct flight connections
connections = {
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

# Add constraints for transitions between cities
for i in range(len(cities) - 1):
    city1, city2 = list(cities.keys())[i], list(cities.keys())[i + 1]
    if (city1, city2) not in connections and (city2, city1) not in connections:
        solver.add(start_days[city1] + cities[city1] < start_days[city2])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for city, duration in cities.items():
        start_day = model[start_days[city]].as_long()
        for day in range(start_day, start_day + duration):
            itinerary.append((day, city))
    itinerary.sort()
    itinerary_dict = {day: city for day, city in itinerary}
    final_itinerary = {f"Day {day}": city for day, city in itinerary_dict.items()}
    print(json.dumps({"itinerary": final_itinerary}, indent=4))
else:
    print("No solution found")