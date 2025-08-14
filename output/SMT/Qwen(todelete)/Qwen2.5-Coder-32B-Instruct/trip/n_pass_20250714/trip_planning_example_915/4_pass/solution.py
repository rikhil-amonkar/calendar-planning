from z3 import *

# Define the solver
solver = Solver()

# Define the cities and their respective stay durations
cities = {
    "Bucharest": 3,
    "Venice": 5,
    "Prague": 4,
    "Frankfurt": 5,
    "Zurich": 5,
    "Florence": 5,
    "Tallinn": 5
}

# Define the events and their respective time windows
events = {
    "Venice Wedding": (22, 26),
    "Frankfurt Show": (12, 16),
    "Tallinn Friends": (8, 12)
}

# Define the direct flight connections
flights = [
    ("Prague", "Tallinn"),
    ("Prague", "Zurich"),
    ("Florence", "Prague"),
    ("Frankfurt", "Bucharest"),
    ("Frankfurt", "Venice"),
    ("Prague", "Bucharest"),
    ("Bucharest", "Zurich"),
    ("Tallinn", "Frankfurt"),
    ("Zurich", "Florence"),
    ("Frankfurt", "Zurich"),
    ("Zurich", "Venice"),
    ("Florence", "Frankfurt"),
    ("Prague", "Frankfurt"),
    ("Tallinn", "Zurich")
]

# Create integer variables for the start day of each city
start_days = {city: Int(f"start_{city}") for city in cities}

# Add constraints for each city's start day and duration
for city, duration in cities.items():
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] + duration <= 26)

# Add constraints for specific events
solver.add(start_days["Venice"] + cities["Venice"] - 1 >= events["Venice Wedding"][0])
solver.add(start_days["Venice"] <= events["Venice Wedding"][1])

solver.add(start_days["Frankfurt"] + cities["Frankfurt"] - 1 >= events["Frankfurt Show"][0])
solver.add(start_days["Frankfurt"] <= events["Frankfurt Show"][1])

solver.add(start_days["Tallinn"] + cities["Tallinn"] - 1 >= events["Tallinn Friends"][0])
solver.add(start_days["Tallinn"] <= events["Tallinn Friends"][1])

# Add constraints for direct flights
for city1, city2 in flights:
    # If we are in city1, we must fly to city2 before leaving city1 or after arriving in city2
    solver.add(Or(
        start_days[city2] >= start_days[city1] + cities[city1],
        start_days[city1] >= start_days[city2] + cities[city2]
    ))

# Ensure the itinerary covers exactly 26 days
# Create a variable for the last day of the itinerary
last_day = Int("last_day")

# Add constraints to determine the last day of the itinerary
for city, duration in cities.items():
    solver.add(last_day >= start_days[city] + duration - 1)

# Ensure the last day is exactly 26
solver.add(last_day == 26)

# Ensure no overlapping stays in different cities
for i, (city1, duration1) in enumerate(cities.items()):
    for j, (city2, duration2) in enumerate(cities.items()):
        if i < j:
            solver.add(Or(
                start_days[city1] + duration1 <= start_days[city2],
                start_days[city2] + duration2 <= start_days[city1]
            ))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for city, start_day in start_days.items():
        start = model.evaluate(start_day).as_long()
        end = start + cities[city] - 1
        if start == end:
            itinerary.append({"day_range": f"Day {start}", "place": city})
        else:
            itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
            itinerary.append({"day_range": f"Day {end}", "place": city})

    # Sort the itinerary by day
    itinerary.sort(key=lambda x: int(x["day_range"].split()[1].split('-')[0]))

    # Output the result as JSON
    print({"itinerary": itinerary})
else:
    print("No solution found")