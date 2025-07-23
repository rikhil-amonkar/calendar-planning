from z3 import *

# Define the cities and their respective stay durations
cities = {
    "Mykonos": 4,
    "Krakow": 5,
    "Vilnius": 2,
    "Helsinki": 2,
    "Dubrovnik": 3,
    "Oslo": 2,
    "Madrid": 5,
    "Paris": 2
}

# Define the direct flight connections
flights = {
    ("Oslo", "Krakow"), ("Oslo", "Paris"), ("Paris", "Madrid"), ("Helsinki", "Vilnius"),
    ("Oslo", "Madrid"), ("Oslo", "Helsinki"), ("Helsinki", "Krakow"), ("Dubrovnik", "Helsinki"),
    ("Dubrovnik", "Madrid"), ("Oslo", "Dubrovnik"), ("Krakow", "Paris"), ("Madrid", "Mykonos"),
    ("Oslo", "Vilnius"), ("Krakow", "Vilnius"), ("Helsinki", "Paris"), ("Vilnius", "Paris"),
    ("Helsinki", "Madrid")
}

# Create a solver instance
solver = Solver()

# Define the start day for each city as a variable
start_days = {city: Int(f"start_{city}") for city in cities}

# Add constraints for each city
for city, duration in cities.items():
    # Each city must start on a day between 1 and 18 - duration + 1
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] <= 18 - duration + 1)

# Specific constraints for Mykonos
solver.add(start_days["Mykonos"] >= 15)
solver.add(start_days["Mykonos"] <= 18 - 4 + 1)

# Specific constraints for Krakow
# No specific constraints for Krakow other than the general ones

# Specific constraints for Vilnius
# No specific constraints for Vilnius other than the general ones

# Specific constraints for Helsinki
# No specific constraints for Helsinki other than the general ones

# Specific constraints for Dubrovnik
solver.add(start_days["Dubrovnik"] >= 2)
solver.add(start_days["Dubrovnik"] <= 4 - 3 + 1)

# Specific constraints for Oslo
solver.add(start_days["Oslo"] >= 1)
solver.add(start_days["Oslo"] <= 2 - 2 + 1)

# Specific constraints for Madrid
# No specific constraints for Madrid other than the general ones

# Specific constraints for Paris
# No specific constraints for Paris other than the general ones

# Add constraints for flight connections
for city1, duration1 in cities.items():
    for city2, duration2 in cities.items():
        if city1 != city2 and (city1, city2) in flights:
            # If you start in city1 and then fly to city2, you must finish city1 before starting city2
            solver.add(Or(start_days[city1] + duration1 <= start_days[city2], start_days[city2] + duration2 <= start_days[city1]))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for city, duration in cities.items():
        start_day = model[start_days[city]].as_long()
        itinerary.extend([(day, city) for day in range(start_day, start_day + duration)])
    itinerary.sort(key=lambda x: x[0])
    itinerary_dict = {f"Day {day}": city for day, city in itinerary}
    print(json.dumps({"itinerary": itinerary_dict}, indent=4))
else:
    print("No solution found")