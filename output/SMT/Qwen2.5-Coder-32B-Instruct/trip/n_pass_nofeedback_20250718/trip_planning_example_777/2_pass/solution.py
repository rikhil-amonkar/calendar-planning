from z3 import *

# Define the cities and their required stay durations
cities = {
    "Dublin": 5,
    "Helsinki": 3,
    "Riga": 3,
    "Reykjavik": 2,
    "Vienna": 2,
    "Tallinn": 5
}

# Define the constraints for specific events
constraints = {
    "Helsinki": (3, 5),  # Meet friends between day 3 and day 5
    "Vienna": (2, 3),   # Attend show between day 2 and day 3
    "Tallinn": (7, 11)  # Attend wedding between day 7 and day 11
}

# Define the direct flights between cities
flights = {
    ("Helsinki", "Riga"),
    ("Riga", "Tallinn"),
    ("Vienna", "Helsinki"),
    ("Riga", "Dublin"),
    ("Vienna", "Riga"),
    ("Reykjavik", "Vienna"),
    ("Helsinki", "Dublin"),
    ("Tallinn", "Dublin"),
    ("Reykjavik", "Helsinki"),
    ("Reykjavik", "Dublin"),
    ("Helsinki", "Tallinn"),
    ("Vienna", "Dublin")
}

# Create a solver instance
solver = Solver()

# Define the start day for each city as a Z3 integer variable
start_days = {city: Int(f"start_{city}") for city in cities}

# Add constraints for the minimum and maximum days for each city
for city, days in cities.items():
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] + days - 1 <= 15)

# Add constraints for specific events
solver.add(start_days["Helsinki"] + 2 >= constraints["Helsinki"][0])  # Day 3
solver.add(start_days["Helsinki"] + 2 <= constraints["Helsinki"][1])  # Day 5
solver.add(start_days["Vienna"] + 1 >= constraints["Vienna"][0])     # Day 2
solver.add(start_days["Vienna"] + 1 <= constraints["Vienna"][1])     # Day 3
solver.add(start_days["Tallinn"] + 6 >= constraints["Tallinn"][0])   # Day 7
solver.add(start_days["Tallinn"] + 6 <= constraints["Tallinn"][1])   # Day 11

# Add constraints for direct flights
for (city1, city2) in flights:
    # If you start in city1 and want to go to city2, you must start city2 after city1 ends
    solver.add(Or(start_days[city1] + cities[city1] < start_days[city2],
                  start_days[city2] + cities[city2] < start_days[city1]))

# Add constraint to ensure all days are covered
days_covered = [False] * 15
for d in range(1, 16):
    day_constraint = Or([And(start_days[city] <= d, start_days[city] + cities[city] - 1 >= d) for city in cities])
    solver.add(day_constraint)
    days_covered[d-1] = day_constraint

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for d in range(1, 16):
        for city in cities:
            if model.evaluate(start_days[city] <= d) and model.evaluate(start_days[city] + cities[city] - 1 >= d):
                itinerary.append((d, city))
                break
    itinerary_dict = {"itinerary": [{"day": d, "place": city} for d, city in itinerary]}
    print(itinerary_dict)
else:
    print("No solution found")