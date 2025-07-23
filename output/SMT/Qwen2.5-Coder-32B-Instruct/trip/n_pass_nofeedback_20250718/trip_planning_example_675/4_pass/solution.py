from z3 import *
import json

# Define the cities and their respective stay durations
cities = {
    "Dubrovnik": 4,
    "Split": 3,
    "Milan": 3,
    "Porto": 4,
    "Krakow": 2,
    "Munich": 5
}

# Define the constraints
constraints = [
    (11, 13, "Milan"),  # Wedding in Milan between day 11 and day 13
    (8, 9, "Krakow"),   # Meet friends in Krakow between day 8 and day 9
    (4, 8, "Munich")    # Annual show in Munich between day 4 and day 8
]

# Define the direct flights
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

# Create a solver
solver = Solver()

# Define the start day for each city as a variable
start_days = {city: Int(f"start_{city}") for city in cities}

# Add constraints for the start days
for city, duration in cities.items():
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] + duration <= 16)

# Add constraints for the specific events
for start, end, city in constraints:
    solver.add(start_days[city] <= start)
    solver.add(start_days[city] + cities[city] >= end + 1)

# Add constraints for the direct flights
for (city1, city2) in flights:
    # If you are in city1 and city2, the days must overlap
    solver.add(Or(start_days[city1] + cities[city1] <= start_days[city2],
                  start_days[city2] + cities[city2] <= start_days[city1]))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    print("Model found:")
    for city, duration in cities.items():
        start_day = model[start_days[city]].as_long()
        print(f"{city}: Start day {start_day}, Duration {duration}")
    
    itinerary = {}
    for city, duration in cities.items():
        start_day = model[start_days[city]].as_long()
        for day in range(start_day, start_day + duration):
            if day in itinerary:
                itinerary[day].append(city)
            else:
                itinerary[day] = [city]
    
    # Convert itinerary to the required format
    result = []
    for day in sorted(itinerary.keys()):
        for city in itinerary[day]:
            result.append({"day": day, "place": city})
    
    print(json.dumps({"itinerary": result}, indent=4))
else:
    print("No solution found")