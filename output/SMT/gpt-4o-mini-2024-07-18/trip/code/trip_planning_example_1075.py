from z3 import *

# Define the number of days and cities
total_days = 25
cities = ["Vienna", "Lyon", "Edinburgh", "Reykjavik", "Stuttgart", "Manchester", "Split", "Prague"]

# Days assigned to each city with constraints
stay_duration = {
    "Vienna": 4,
    "Lyon": 3,
    "Edinburgh": 4,
    "Reykjavik": 5,
    "Stuttgart": 5,
    "Manchester": 2,
    "Split": 5,
    "Prague": 4
}

# Constraints for specific events
annual_show_days_edinburgh = list(range(5, 9))  # Attend the annual show in Edinburgh (Day 5 to Day 8)
wedding_days_split = list(range(19, 24))          # Wedding in Split (Day 19 to Day 23)

# Define direct flights between the cities
flights = {
    "Reykjavik": ["Stuttgart", "Vienna"],
    "Stuttgart": ["Split", "Vienna", "Edinburgh", "Manchester"],
    "Lyon": ["Vienna", "Split"],
    "Edinburgh": ["Prague"],
    "Manchester": ["Prague", "Split"],
    "Split": ["Lyon", "Manchester", "Stuttgart"],
    "Prague": ["Manchester", "Edinburgh", "Vienna"],
    "Vienna": ["Manchester", "Stuttgart", "Prague", "Lyon"]
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

# Annual show in Edinburgh during day 5 to day 8
for day in annual_show_days_edinburgh:
    solver.add(trip[day - 1] == cities.index("Edinburgh"))  # Day - 1 for 0-based index

# Wedding in Split during day 19 to day 23
for day in wedding_days_split:
    solver.add(trip[day - 1] == cities.index("Split"))  # Day - 1 for 0-based index

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