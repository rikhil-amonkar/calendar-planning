from z3 import *

# Define the number of days and cities
total_days = 15
cities = [
    "Paris", "Madrid", "Bucharest", "Seville"
]

# Days assigned to each city with constraints
stay_duration = {
    "Paris": 6,
    "Madrid": 7,
    "Bucharest": 2,
    "Seville": 3
}

# Constraints for specific events
annual_show_days_madrid = range(1, 8)        # Annual show in Madrid (Day 1 to Day 7)
relatives_visit_days_bucharest = range(14, 16)  # Visiting relatives in Bucharest (Day 14 to Day 15)

# Define direct flights between the cities
flights = {
    "Paris": ["Bucharest", "Seville", "Madrid"],
    "Madrid": ["Bucharest", "Seville", "Paris"],
    "Bucharest": ["Paris", "Madrid"],
    "Seville": ["Madrid", "Paris"]
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

# Annual show in Madrid between day 1 and day 7
for day in annual_show_days_madrid:
    solver.add(trip[day - 1] == cities.index("Madrid"))  # Adjust for 0-based index

# Visiting relatives in Bucharest between day 14 and day 15
for day in relatives_visit_days_bucharest:
    solver.add(trip[day - 1] == cities.index("Bucharest"))  # Adjust for 0-based index

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