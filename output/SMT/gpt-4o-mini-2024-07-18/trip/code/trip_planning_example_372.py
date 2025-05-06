from z3 import *

# Define the number of days and cities
total_days = 13
cities = [
    "Seville", "Stuttgart", "Porto", "Madrid"
]

# Days assigned to each city with constraints
stay_duration = {
    "Seville": 2,
    "Stuttgart": 7,
    "Porto": 3,
    "Madrid": 4
}

# Constraints for specific events
conference_days_stuttgart = [7, 13]  # Conference in Stuttgart (Day 7 and Day 13)
relatives_visit_days_madrid = range(1, 5)  # Visiting relatives in Madrid (Day 1 to Day 4)

# Define direct flights between the cities
flights = {
    "Porto": ["Stuttgart", "Madrid", "Seville"],
    "Seville": ["Porto", "Madrid"],
    "Stuttgart": ["Porto"],
    "Madrid": ["Porto", "Seville"]
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

# Conference attendance in Stuttgart on day 7 and day 13
for day in conference_days_stuttgart:
    solver.add(trip[day - 1] == cities.index("Stuttgart"))  # Adjust for 0-based index

# Visiting relatives in Madrid between day 1 and day 4
for day in relatives_visit_days_madrid:
    solver.add(trip[day - 1] == cities.index("Madrid"))  # Adjust for 0-based index

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