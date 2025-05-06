from z3 import *

# Define the number of days and cities
total_days = 17
cities = ["Vilnius", "Naples", "Vienna"]

# Days assigned to each city with constraints
stay_duration = {
    "Vilnius": 7,
    "Naples": 5,
    "Vienna": 7
}

# Constraints for specific events
relatives_visit_days_naples = range(1, 6)  # Visit relatives in Naples between day 1 and day 5

# Define direct flights between the cities
flights = {
    "Naples": ["Vienna"],
    "Vienna": ["Vilnius", "Naples"],
    "Vilnius": ["Vienna"]
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for each day
trip = [Int(f'day_{i + 1}') for i in range(total_days)]

# Each day must refer to one of the cities
for day in trip:
    solver.add(Or([day == cities.index(city) for city in cities]))

# Count the days spent in each city
city_count = {city: Sum([If(trip[day] == cities.index(city), 1, 0) for day in range(total_days)]) for city in cities}

# Enforce stay durations
for city, duration in stay_duration.items():
    solver.add(city_count[city] == duration)

# Visit relatives in Naples between day 1 and day 5
for day in relatives_visit_days_naples:
    solver.add(trip[day - 1] == cities.index("Naples"))  # Adjust for 0-based index

# Define direct flight connections
for day in range(total_days - 1):
    curr_city_index = trip[day]
    next_city_index = trip[day + 1]
    curr_city = cities[curr_city_index]
    next_city = cities[next_city_index]
    # If transitioning from one city to another, it must be a valid flight
    solver.add(Or([And(curr_city_index == cities.index(city), next_city_index == cities.index(next_city_city))
                    for city in cities for next_city_city in flights[city]]))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    for day in range(total_days):
        print(f"Day {day + 1}: {cities[model[trip[day]].as_long()]}")
else:
    print("No valid trip plan found.")