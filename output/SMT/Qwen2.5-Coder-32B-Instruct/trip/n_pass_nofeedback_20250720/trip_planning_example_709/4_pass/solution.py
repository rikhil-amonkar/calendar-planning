from z3 import *
import json

# Define the solver
solver = Solver()

# Define the number of days
total_days = 18

# Define the cities and their respective stay durations
cities = {
    "Helsinki": 4,
    "Valencia": 5,
    "Dubrovnik": 4,
    "Porto": 3,
    "Prague": 3,
    "Reykjavik": 4
}

# Define the direct flight connections
flights = {
    ("Helsinki", "Prague"),
    ("Prague", "Valencia"),
    ("Valencia", "Porto"),
    ("Helsinki", "Reykjavik"),
    ("Dubrovnik", "Helsinki"),
    ("Reykjavik", "Prague")
}

# Create variables for the start day of each city
start_days = {city: Int(f"start_{city}") for city in cities}

# Add constraints for the start days
for city, duration in cities.items():
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] + duration <= total_days)

# Add constraints for the friend meeting in Porto between day 16 and day 18
solver.add(start_days["Porto"] + cities["Porto"] - 1 >= 16)
solver.add(start_days["Porto"] <= 18)

# Define the sequence of cities and ensure valid transitions
# We need to ensure that the transitions are valid based on the direct flight connections
# We will use a list to represent the sequence of cities
sequence = ["Dubrovnik", "Helsinki", "Reykjavik", "Prague", "Valencia", "Porto"]

# Add constraints for the sequence
for i in range(len(sequence) - 1):
    city1 = sequence[i]
    city2 = sequence[i + 1]
    if (city1, city2) in flights:
        solver.add(start_days[city2] >= start_days[city1] + cities[city1])
    elif (city2, city1) in flights:
        solver.add(start_days[city1] >= start_days[city2] + cities[city2])
    else:
        solver.add(False)  # This should never happen if the sequence is valid

# Ensure that each city is visited exactly once
for i, city1 in enumerate(cities):
    for j, city2 in enumerate(cities):
        if i < j:
            solver.add(Or(start_days[city1] + cities[city1] <= start_days[city2],
                          start_days[city2] + cities[city2] <= start_days[city1]))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for day in range(1, total_days + 1):
        for city in cities:
            start_day = model[start_days[city]].as_long()
            end_day = start_day + cities[city] - 1
            if start_day <= day <= end_day:
                itinerary.append({"day": day, "place": city})
                break
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found")