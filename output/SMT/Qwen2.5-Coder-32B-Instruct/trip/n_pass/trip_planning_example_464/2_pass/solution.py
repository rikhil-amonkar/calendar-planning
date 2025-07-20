from z3 import *
import json

# Define the solver
solver = Solver()

# Define the number of days
total_days = 18

# Define the cities and their required stay durations
cities = {
    "Krakow": 5,
    "Frankfurt": 4,
    "Oslo": 3,
    "Dubrovnik": 5,
    "Naples": 5
}

# Define the constraints for visiting relatives in Oslo and meeting friends in Dubrovnik
oslo_relative_days = (16, 18)
dubrovnik_friends_days = (5, 9)

# Define the direct flight connections
connections = {
    "Dubrovnik": ["Oslo", "Frankfurt"],
    "Oslo": ["Dubrovnik", "Frankfurt", "Krakow", "Naples"],
    "Frankfurt": ["Dubrovnik", "Oslo", "Krakow"],
    "Krakow": ["Frankfurt", "Oslo"],
    "Naples": ["Oslo", "Dubrovnik", "Frankfurt"]
}

# Create variables for the start day of each city
start_days = {city: Int(f"start_{city}") for city in cities}

# Add constraints for the start days
for city, duration in cities.items():
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] + duration <= total_days)

# Add constraints for the required days in Oslo and Dubrovnik
oslo_start = start_days["Oslo"]
dubrovnik_start = start_days["Dubrovnik"]

# Ensure Oslo visit includes days 16-18
oslo_overlap = Or([And(oslo_start + i >= oslo_relative_days[0], oslo_start + i <= oslo_relative_days[1]) for i in range(cities["Oslo"])])
solver.add(oslo_overlap)

# Ensure Dubrovnik visit includes days 5-9
dubrovnik_overlap = Or([And(dubrovnik_start + i >= dubrovnik_friends_days[0], dubrovnik_start + i <= dubrovnik_friends_days[1]) for i in range(cities["Dubrovnik"])])
solver.add(dubrovnik_overlap)

# Add constraints for the transitions between cities
for city, duration in cities.items():
    for other_city in connections[city]:
        if other_city != city:
            solver.add(Or(start_days[city] + duration < start_days[other_city], start_days[other_city] + cities[other_city] < start_days[city]))

# Add constraints to ensure no overlap in days between cities
for i, city1 in enumerate(cities):
    for city2 in list(cities.keys())[i+1:]:
        solver.add(Or(start_days[city1] + cities[city1] <= start_days[city2], start_days[city2] + cities[city2] <= start_days[city1]))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for day in range(1, total_days + 1):
        for city in cities:
            start_day = model[start_days[city]].as_long()
            if start_day <= day <= start_day + cities[city]:
                itinerary.append({"day": day, "place": city})
                break
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found")