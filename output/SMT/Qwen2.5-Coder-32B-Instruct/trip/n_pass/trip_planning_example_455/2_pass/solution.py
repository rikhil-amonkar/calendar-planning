from z3 import *
import json

# Define the solver
solver = Solver()

# Define the number of days
total_days = 21

# Define the cities and their required stay durations
cities = {
    "Reykjavik": 7,
    "Riga": 2,
    "Warsaw": 3,
    "Istanbul": 6,
    "Krakow": 7
}

# Define the constraints for specific events
friend_meeting_days = (1, 2)  # Riga
wedding_days = (2, 7)        # Istanbul

# Define the direct flight connections
connections = {
    ("Istanbul", "Krakow"),
    ("Warsaw", "Reykjavik"),
    ("Istanbul", "Warsaw"),
    ("Riga", "Istanbul"),
    ("Krakow", "Warsaw"),
    ("Riga", "Warsaw")
}

# Create variables for the start day of each city
start_days = {city: Int(f"start_{city}") for city in cities}

# Add constraints for the start days
for city, days in cities.items():
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] + days <= total_days)

# Add constraints for the specific events
# Friend meeting in Riga between day 1 and day 2
solver.add(Or(start_days["Riga"] + 1 >= friend_meeting_days[0],
              start_days["Riga"] <= friend_meeting_days[1]))

# Wedding in Istanbul between day 2 and day 7
solver.add(Or(start_days["Istanbul"] + 1 >= wedding_days[0],
              start_days["Istanbul"] <= wedding_days[1]))

# Add constraints for the direct flight connections
for city1, city2 in connections:
    # If you start city1 on day X, you can only start city2 on day X+days_in_city1 or later
    solver.add(Or(start_days[city1] + cities[city1] <= start_days[city2],
                  start_days[city2] + cities[city2] <= start_days[city1]))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for city in cities:
        start_day = model[start_days[city]].as_long()
        itinerary.extend([(day, city) for day in range(start_day, start_day + cities[city])])
    itinerary.sort(key=lambda x: x[0])
    itinerary_dict = {"itinerary": [{"day": day, "place": place} for day, place in itinerary]}
    print(json.dumps(itinerary_dict, indent=2))
else:
    print("No solution found")