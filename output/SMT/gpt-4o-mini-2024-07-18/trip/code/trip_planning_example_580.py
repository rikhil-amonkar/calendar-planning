from z3 import *

# Define the number of days and cities
total_days = 23
cities = [
    "Paris", "Oslo", "Porto", 
    "Geneva", "Reykjavik"
]

# Days assigned to each city with constraints
stay_duration = {
    "Paris": 6,
    "Oslo": 5,
    "Porto": 7,
    "Geneva": 7,
    "Reykjavik": 2
}

# Constraints for specific events
conference_days_geneva = [1, 7]       # Conferences in Geneva (Day 1 and Day 7)
relatives_visit_days_oslo = range(19, 24)  # Visiting relatives in Oslo (Day 19 to Day 23)

# Define direct flights between the cities
flights = {
    "Paris": ["Oslo", "Porto", "Reykjavik", "Geneva"],
    "Oslo": ["Paris", "Geneva", "Porto", "Reykjavik"],
    "Porto": ["Paris", "Oslo", "Geneva"],
    "Geneva": ["Oslo", "Paris", "Porto"],
    "Reykjavik": ["Paris", "Oslo"]
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

# Conferences in Geneva on day 1 and day 7
for day in conference_days_geneva:
    solver.add(trip[day - 1] == cities.index("Geneva"))  # Adjust for 0-based index

# Visiting relatives in Oslo between day 19 and day 23
for day in relatives_visit_days_oslo:
    solver.add(trip[day - 1] == cities.index("Oslo"))  # Adjust for 0-based index

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