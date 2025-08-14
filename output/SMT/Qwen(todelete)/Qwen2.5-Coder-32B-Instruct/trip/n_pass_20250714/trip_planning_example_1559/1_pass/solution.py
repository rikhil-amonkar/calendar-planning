from z3 import *

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

# Define the constraints
constraints = {
    "Valencia": (3, 4),  # Meet friends between day 3 and 4
    "Oslo": (13, 15),    # Meet friend between day 13 and 15
    "Seville": (5, 9),   # Annual show between day 5 and 9
    "Mykonos": (21, 25)  # Wedding between day 21 and 25
}

# Define direct flight connections
flight_connections = [
    ("Lisbon", "Paris"), ("Lyon", "Nice"), ("Tallinn", "Oslo"), ("Prague", "Lyon"),
    ("Paris", "Oslo"), ("Lisbon", "Seville"), ("Prague", "Lisbon"), ("Oslo", "Nice"),
    ("Valencia", "Paris"), ("Valencia", "Lisbon"), ("Paris", "Nice"), ("Nice", "Mykonos"),
    ("Paris", "Lyon"), ("Valencia", "Lyon"), ("Prague", "Oslo"), ("Prague", "Paris"),
    ("Seville", "Paris"), ("Oslo", "Lyon"), ("Prague", "Valencia"), ("Lisbon", "Nice"),
    ("Lisbon", "Oslo"), ("Valencia", "Seville"), ("Lisbon", "Lyon"), ("Paris", "Tallinn"),
    ("Prague", "Tallinn")
]

# Create a solver instance
solver = Solver()

# Define variables for the start day of each city
start_days = {city: Int(f"start_{city}") for city in cities}

# Add constraints for the start days of each city
for city, duration in cities.items():
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] + duration <= 25)

# Add specific constraints for meeting friends and events
solver.add(And(start_days["Valencia"] + 1 >= 3, start_days["Valencia"] <= 4))
solver.add(And(start_days["Oslo"] + 2 >= 13, start_days["Oslo"] <= 15))
solver.add(And(start_days["Seville"] + 4 >= 5, start_days["Seville"] <= 9))
solver.add(And(start_days["Mykonos"] + 4 >= 21, start_days["Mykonos"] <= 25))

# Add constraints for direct flights
for i, city1 in enumerate(cities):
    for j, city2 in enumerate(cities):
        if i < j and (city1, city2) not in flight_connections and (city2, city1) not in flight_connections:
            solver.add(Or(start_days[city1] + cities[city1] <= start_days[city2], start_days[city2] + cities[city2] <= start_days[city1]))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for city, duration in cities.items():
        start_day = model[start_days[city]].as_long()
        end_day = start_day + duration - 1
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
        if start_day != end_day:
            itinerary.append({"day_range": f"Day {end_day}", "place": city})
    
    # Sort the itinerary by day
    itinerary.sort(key=lambda x: int(x["day_range"].split()[1].split('-')[0]))
    
    # Print the itinerary in JSON format
    print({"itinerary": itinerary})
else:
    print("No solution found")