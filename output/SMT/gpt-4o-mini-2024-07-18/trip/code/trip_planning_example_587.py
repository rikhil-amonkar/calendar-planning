from z3 import *

# Define the number of days and cities
total_days = 21
cities = ["Manchester", "Istanbul", "Venice", "Krakow", "Lyon"]

# Days assigned to each city with constraints
stay_duration = {
    "Manchester": 3,
    "Istanbul": 7,
    "Venice": 7,
    "Krakow": 6,
    "Lyon": 2
}

# Constraints for specific events
wedding_days_manchester = [1, 2, 3]  # Wedding in Manchester between day 1 and day 3
workshop_days_venice = list(range(3, 10))  # Workshop in Venice between day 3 and day 9

# Define direct flights between the cities
flights = {
    "Manchester": ["Venice", "Istanbul", "Krakow"],
    "Istanbul": ["Manchester", "Venice", "Krakow", "Lyon"],
    "Venice": ["Manchester", "Istanbul", "Lyon"],
    "Krakow": ["Istanbul", "Manchester"],
    "Lyon": ["Istanbul", "Venice"]
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

# Wedding in Manchester between day 1 and day 3
for day in wedding_days_manchester:
    solver.add(trip[day - 1] == cities.index("Manchester"))  # Adjust for 0-based index

# Workshop in Venice between day 3 and day 9
for day in workshop_days_venice:
    solver.add(trip[day - 1] == cities.index("Venice"))  # Adjust for 0-based index

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