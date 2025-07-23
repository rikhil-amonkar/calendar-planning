from z3 import *

# Define the cities and their respective stay durations
cities = {
    "Dubrovnik": 4,
    "Split": 3,
    "Milan": 3,
    "Porto": 4,
    "Krakow": 2,
    "Munich": 5
}

# Define the constraints for specific events
constraints = {
    "Milan": (11, 13),  # Wedding in Milan between day 11 and day 13
    "Krakow": (8, 9),   # Meet friends in Krakow between day 8 and day 9
    "Munich": (4, 8)    # Annual show in Munich between day 4 and day 8
}

# Define the direct flights between cities
flights = {
    ("Munich", "Porto"),
    ("Split", "Milan"),
    ("Milan", "Porto"),
    ("Munich", "Krakow"),
    ("Munich", "Milan"),
    ("Dubrovnik", "Munich"),
    ("Krakow", "Split"),
    ("Krakow", "Milan"),
    ("Munich", "Split")
}

# Create a solver instance
solver = Solver()

# Define the start day for each city as a Z3 integer variable
start_days = {city: Int(f"start_{city}") for city in cities}

# Add constraints for the start days
for city, duration in cities.items():
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] + duration <= 16)

# Add constraints for specific events
solver.add(start_days["Milan"] + 2 >= 11)  # Milan: day 11-13, so start must be at least 11-2=9
solver.add(start_days["Milan"] <= 11)      # Milan: day 11-13, so start must be at most 11
solver.add(start_days["Krakow"] + 1 >= 8)  # Krakow: day 8-9, so start must be at least 8-1=7
solver.add(start_days["Krakow"] <= 8)      # Krakow: day 8-9, so start must be at most 8
solver.add(start_days["Munich"] + 4 >= 4)  # Munich: day 4-8, so start must be at least 4-4=0, but >=1
solver.add(start_days["Munich"] <= 4)      # Munich: day 4-8, so start must be at most 4

# Add constraints for direct flights
for (city1, city2) in flights:
    # If you start in city1 and stay for its duration, you can fly to city2 on the last day of city1
    solver.add(Or(start_days[city2] <= start_days[city1] + cities[city1],
                  start_days[city1] <= start_days[city2] + cities[city2]))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for city, start in start_days.items():
        start_day = model[start].as_long()
        end_day = start_day + cities[city] - 1
        for day in range(start_day, end_day + 1):
            itinerary.append((day, city))
    itinerary.sort()
    itinerary_dict = {f"Day {day}": city for day, city in itinerary}
    print(json.dumps({"itinerary": itinerary_dict}, indent=2))
else:
    print("No solution found")