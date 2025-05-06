from z3 import *

# Define the number of days and cities
total_days = 24
cities = [
    "Venice", "Reykjavik", "Munich", "Santorini",
    "Manchester", "Porto", "Bucharest", "Tallinn",
    "Valencia", "Vienna"
]

# Days assigned to each city with constraints
stay_duration = {
    "Venice": 3,
    "Reykjavik": 2,
    "Munich": 3,
    "Santorini": 3,
    "Manchester": 3,
    "Porto": 3,
    "Bucharest": 5,
    "Tallinn": 4,
    "Valencia": 2,
    "Vienna": 5
}

# Constraints for specific events
annual_show_days_munich = [4, 5, 6]  # Annual show from day 4 to day 6 in Munich
relatives_visit_days_santorini = [8, 9, 10]  # Visit relatives in Santorini between day 8 and day 10
workshop_days_valencia = [14, 15]  # Workshop from day 14 to day 15 in Valencia

# Define direct flights between the cities
flights = {
    "Bucharest": ["Manchester", "Valencia", "Vienna", "Santorini"],
    "Manchester": ["Bucharest", "Santorini", "Vienna", "Porto", "Munich"],
    "Munich": ["Venice", "Porto", "Reykjavik", "Valencia", "Bucharest", "Vienna", "Manchester", "Tallinn"],
    "Venice": ["Munich", "Santorini", "Vienna", "Manchester"],
    "Santorini": ["Venice", "Manchester", "Bucharest", "Vienna"],
    "Reykjavik": ["Munich", "Vienna"],
    "Porto": ["Munich", "Manchester", "Valencia", "Vienna"],
    "Valencia": ["Bucharest", "Porto", "Munich", "Vienna"],
    "Tallinn": ["Munich"],
    "Vienna": ["Reykjavik", "Bucharest", "Porto", "Valencia", "Munich", "Santorini", "Manchester", "Venice"],
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for each day
trip = [Int(f'day_{i + 1}') for i in range(total_days)]

# Each day must refer to one of the cities
for day in trip:
    solver.add(Or([day == cities.index(city) for city in cities]))

# Count the days spent in each city
city_count = {
    city: Sum([If(trip[day] == cities.index(city), 1, 0) for day in range(total_days)])
    for city in cities
}

# Enforce stay durations
for city, duration in stay_duration.items():
    solver.add(city_count[city] == duration)

# Annual show in Munich between day 4 and day 6
for day in annual_show_days_munich:
    solver.add(trip[day - 1] == cities.index("Munich"))

# Visiting relatives in Santorini between day 8 and day 10
for day in relatives_visit_days_santorini:
    solver.add(trip[day - 1] == cities.index("Santorini"))

# Workshop in Valencia between day 14 and day 15
for day in workshop_days_valencia:
    solver.add(trip[day - 1] == cities.index("Valencia"))

# Define direct flight connections
for day in range(total_days - 1):
    curr_city_index = trip[day]
    next_city_index = trip[day + 1]
    curr_city = cities[curr_city_index]
    next_city = cities[next_city_index]
    # If transitioning from one city to another, it must be a valid flight
    solver.add(Or([
        And(curr_city_index == cities.index(city), next_city_index == cities.index(next_city_city))
        for city in cities for next_city_city in flights[city]
    ]))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    for day in range(total_days):
        print(f"Day {day + 1}: {cities[model[trip[day]].as_long()]}")
else:
    print("No valid trip plan found.")