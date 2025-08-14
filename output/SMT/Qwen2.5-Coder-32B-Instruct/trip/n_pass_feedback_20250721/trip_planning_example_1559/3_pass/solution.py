from z3 import *
import json

# Define the solver
solver = Solver()

# Define the cities and their respective stay durations
cities = {
    "Valencia": 2,
    "Oslo": 3,
    "Lyon": 4,
    "Prague": 3,
    "Paris": 4,
    "Nice": 4,
    "Seville": 5,
    "Tallinn": 2,
    "Mykonos": 5,
    "Lisbon": 2
}

# Define the constraints for specific cities
constraints = {
    "Valencia": (3, 4),  # Meet friends between day 3 and 4
    "Oslo": (13, 15),    # Meet friend between day 13 and 15
    "Seville": (5, 9),   # Attend show between day 5 and 9
    "Mykonos": (21, 25)  # Attend wedding between day 21 and 25
}

# Define the direct flight connections
flights = {
    ("Lisbon", "Paris"), ("Lyon", "Nice"), ("Tallinn", "Oslo"), ("Prague", "Lyon"),
    ("Paris", "Oslo"), ("Lisbon", "Seville"), ("Prague", "Lisbon"), ("Oslo", "Nice"),
    ("Valencia", "Paris"), ("Valencia", "Lisbon"), ("Paris", "Nice"), ("Nice", "Mykonos"),
    ("Paris", "Lyon"), ("Valencia", "Lyon"), ("Prague", "Oslo"), ("Prague", "Paris"),
    ("Seville", "Paris"), ("Oslo", "Lyon"), ("Prague", "Valencia"), ("Lisbon", "Nice"),
    ("Lisbon", "Oslo"), ("Valencia", "Seville"), ("Lisbon", "Lyon"), ("Paris", "Tallinn"),
    ("Prague", "Tallinn")
}

# Create integer variables for the start day of each city visit
start_days = {city: Int(f"start_{city}") for city in cities}

# Add constraints for each city
for city, duration in cities.items():
    # Ensure the city visit is within the 25-day period
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] + duration - 1 <= 25)

    # Add specific constraints if any
    if city in constraints:
        meet_start, meet_end = constraints[city]
        solver.add(start_days[city] <= meet_start)
        solver.add(start_days[city] + duration - 1 >= meet_end)

# Add constraints for direct flights
for (city1, city2) in flights:
    # If you visit city1 and city2, the visit days must overlap
    solver.add(Or(start_days[city1] + cities[city1] - 1 < start_days[city2],
                 start_days[city2] + cities[city2] - 1 < start_days[city1],
                 And(start_days[city1] + cities[city1] - 1 == start_days[city2],
                     start_days[city2] + cities[city2] - 1 == start_days[city1] + cities[city1] - 1)))

# Ensure no gaps between visits
for i, city1 in enumerate(cities):
    for j, city2 in enumerate(cities):
        if i < j and (city1, city2) in flights:
            # Ensure that the end of city1's visit is the start of city2's visit
            solver.add(Or(start_days[city1] + cities[city1] - 1 < start_days[city2],
                         start_days[city2] + cities[city2] - 1 < start_days[city1],
                         start_days[city1] + cities[city1] == start_days[city2]))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for city, start_day in start_days.items():
        start = model[start_day].as_long()
        end = start + cities[city] - 1
        for day in range(start, end + 1):
            itinerary.append((day, city))
    itinerary.sort()
    itinerary_dict = {f"Day {day}": city for day, city in itinerary}
    print(json.dumps({"itinerary": itinerary_dict}, indent=4))
else:
    print("No solution found")