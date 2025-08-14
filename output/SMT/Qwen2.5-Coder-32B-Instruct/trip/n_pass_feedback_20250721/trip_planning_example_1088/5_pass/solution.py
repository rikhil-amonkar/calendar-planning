from z3 import *

# Define the cities and their required stay durations
cities = {
    "Oslo": 5,
    "Stuttgart": 5,
    "Reykjavik": 2,
    "Split": 3,
    "Geneva": 2,
    "Porto": 3,
    "Tallinn": 5,
    "Stockholm": 3
}

# Define the direct flight connections
flights = {
    "Reykjavik": ["Stuttgart", "Stockholm", "Tallinn"],
    "Stockholm": ["Oslo", "Stuttgart", "Reykjavik", "Split", "Geneva", "Porto"],
    "Stuttgart": ["Reykjavik", "Porto", "Oslo", "Stockholm", "Split", "Geneva"],
    "Oslo": ["Reykjavik", "Stuttgart", "Split", "Geneva", "Porto", "Tallinn"],
    "Split": ["Oslo", "Stockholm", "Stuttgart", "Geneva", "Porto"],
    "Geneva": ["Oslo", "Stuttgart", "Stockholm", "Split", "Porto"],
    "Porto": ["Oslo", "Stuttgart", "Stockholm", "Split", "Geneva"],
    "Tallinn": ["Oslo", "Reykjavik"]
}

# Create a solver instance
solver = Solver()

# Define the start day for each city as a Z3 integer variable
start_days = {city: Int(f"start_{city}") for city in cities}

# Add constraints for the required stay durations
for city, duration in cities.items():
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] + duration <= 21)

# Add constraints for the specific days in certain cities
solver.add(start_days["Reykjavik"] == 1)  # Conference in Reykjavik on day 1 and 2
solver.add(start_days["Porto"] >= 19)     # Workshop in Porto between day 19 and 21

# Add constraints for the friend meeting in Stockholm
solver.add(start_days["Stockholm"] <= 3)  # Meet friend in Stockholm between day 2 and 4

# Add constraints for the transitions between cities
for city, duration in cities.items():
    for next_city in flights[city]:
        # If we start in city and fly to next_city, we must be in next_city on the day we leave city
        solver.add(Or(start_days[next_city] != start_days[city] + duration,
                     start_days[next_city] <= start_days[city] + duration))

# Add constraints to ensure no overlap in stays except for the transition day
for city1 in cities:
    for city2 in cities:
        if city1 != city2:
            solver.add(Or(start_days[city1] + cities[city1] <= start_days[city2],
                          start_days[city2] + cities[city2] <= start_days[city1]))

# Ensure that the total number of days is exactly 21
# Introduce a variable to represent the last day of the itinerary
last_day = Int('last_day')
solver.add(last_day == 21)

# Ensure that the last day of the last city is within the 21-day limit
for city, duration in cities.items():
    solver.add(start_days[city] + duration <= last_day)

# Introduce a variable to represent the maximum end day
max_end_day = Int('max_end_day')

# Add constraints to ensure that max_end_day is the maximum of all end days
for city, duration in cities.items():
    end_day = start_days[city] + duration
    solver.add(max_end_day >= end_day)

# Ensure that max_end_day is exactly 21
solver.add(max_end_day == 21)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for city in cities:
        start_day = model[start_days[city]].as_long()
        itinerary.extend([(day, city) for day in range(start_day, start_day + cities[city])])
    itinerary.sort(key=lambda x: x[0])
    itinerary_dict = {f"Day {day}": city for day, city in itinerary}
    print(json.dumps({"itinerary": itinerary_dict}, indent=4))
else:
    print("No solution found")