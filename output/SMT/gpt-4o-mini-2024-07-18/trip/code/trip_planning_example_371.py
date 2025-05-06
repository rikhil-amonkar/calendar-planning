from z3 import *

# Define the number of days and cities
total_days = 9
cities = [
    "Nice", "Stockholm", "Split", "Vienna"
]

# Days assigned to each city with constraints
stay_duration = {
    "Nice": 2,
    "Stockholm": 5,
    "Split": 3,
    "Vienna": 2
}

# Constraints for specific events
conference_days_split = [7, 9]             # Conference in Split (Day 7 and Day 9)
workshop_days_vienna = [1, 2]               # Workshop in Vienna (Day 1 and Day 2)

# Define direct flights between the cities
flights = {
    "Vienna": ["Stockholm", "Nice", "Split"],
    "Stockholm": ["Nice", "Split", "Vienna"],
    "Split": ["Vienna", "Stockholm"],
    "Nice": ["Vienna", "Stockholm"]
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

# Conference in Split on day 7 and day 9
for day in conference_days_split:
    solver.add(trip[day - 1] == cities.index("Split"))  # Adjust for 0-based index

# Workshop in Vienna on day 1 and day 2
for day in workshop_days_vienna:
    solver.add(trip[day - 1] == cities.index("Vienna"))  # Adjust for 0-based index

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
    itinerary = []
    for day in range(total_days):
        city = cities[model[trip[day]].as_long()]
        itinerary.append(f"Day {day + 1}: {city}")
    print("\n".join(itinerary))
else:
    print("No valid trip plan found.")