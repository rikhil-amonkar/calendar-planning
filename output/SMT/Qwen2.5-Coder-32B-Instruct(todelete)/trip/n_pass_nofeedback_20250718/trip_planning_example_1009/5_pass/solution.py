from z3 import *
import json

# Define the cities and their respective stay durations
cities = {
    "Riga": 4,
    "Manchester": 5,
    "Bucharest": 4,
    "Florence": 4,
    "Vienna": 2,
    "Istanbul": 2,
    "Reykjavik": 4,
    "Stuttgart": 5
}

# Define the total number of days
total_days = 23

# Define the constraints for specific events
bucharest_workshop_days = (16, 19)
istanbul_show_days = (12, 13)

# Define the direct flight connections
flight_connections = {
    "Bucharest": ["Vienna", "Riga", "Istanbul"],
    "Vienna": ["Bucharest", "Reykjavik", "Manchester", "Riga", "Florence", "Stuttgart"],
    "Reykjavik": ["Vienna", "Stuttgart"],
    "Manchester": ["Vienna", "Riga", "Istanbul", "Bucharest", "Stuttgart"],
    "Riga": ["Bucharest", "Vienna", "Manchester", "Istanbul"],
    "Istanbul": ["Vienna", "Riga", "Stuttgart", "Manchester", "Bucharest"],
    "Florence": ["Vienna"],
    "Stuttgart": ["Vienna", "Reykjavik", "Manchester", "Istanbul"]
}

# Create a solver instance
solver = Solver()

# Define the start day for each city as a Z3 integer variable
start_days = {city: Int(f"start_{city}") for city in cities}

# Add constraints for each city
for city, duration in cities.items():
    # The start day must be non-negative
    solver.add(start_days[city] >= 0)
    # The end day must be within the total number of days
    solver.add(start_days[city] + duration <= total_days)

# Add constraints for the specific events
# Bucharest workshop
solver.add(Or([And(start_days["Bucharest"] + i >= bucharest_workshop_days[0],
                   start_days["Bucharest"] + i <= bucharest_workshop_days[1])
               for i in range(cities["Bucharest"])]))

# Istanbul show
solver.add(Or([And(start_days["Istanbul"] + i >= istanbul_show_days[0],
                   start_days["Istanbul"] + i <= istanbul_show_days[1])
               for i in range(cities["Istanbul"])]))

# Add constraints for direct flights between cities
for city, connections in flight_connections.items():
    for other_city in connections:
        if city != other_city:
            # If you start in city A, you can only start in city B after you finish in city A
            solver.add(Or(start_days[city] + cities[city] <= start_days[other_city],
                           start_days[other_city] + cities[other_city] <= start_days[city]))

# Ensure that the itinerary respects the direct flight connections
for city, duration in cities.items():
    for other_city in cities:
        if city != other_city:
            # If you are in city A, you can only move to city B if there is a direct flight
            if other_city not in flight_connections[city]:
                solver.add(Or(start_days[city] + duration <= start_days[other_city],
                               start_days[other_city] + cities[other_city] <= start_days[city]))

# Ensure that the days are correctly accounted for
itinerary_days = [Bool(f"day_{day}_{city}") for day in range(1, total_days + 1) for city in cities]
itinerary_days_dict = {(day, city): Bool(f"day_{day}_{city}") for day in range(1, total_days + 1) for city in cities}

# Add constraints for each day
for day in range(1, total_days + 1):
    # Each day can only be in one city or traveling
    solver.add(Or([itinerary_days_dict[(day, city)] for city in cities] + [False]))

    # Ensure that the days are correctly assigned to cities
    for city, duration in cities.items():
        for d in range(duration):
            solver.add(Implies(itinerary_days_dict[(day, city)], start_days[city] <= day - 1))
            solver.add(Implies(itinerary_days_dict[(day, city)], day <= start_days[city] + duration))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for day in range(1, total_days + 1):
        for city in cities:
            if model[itinerary_days_dict[(day, city)]]:
                itinerary.append({"day": day, "place": city})
                break
        else:
            itinerary.append({"day": day, "place": "Travel"})
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found")