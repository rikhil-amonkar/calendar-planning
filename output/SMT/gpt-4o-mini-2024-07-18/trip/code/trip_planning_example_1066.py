from z3 import *

# Define the number of days and cities
total_days = 21
cities = [
    "Brussels", "Bucharest", "Stuttgart", 
    "Mykonos", "Madrid", "Helsinki", 
    "Split", "London"
]

# Days assigned to each city with constraints
stay_duration = {
    "Brussels": 4,
    "Bucharest": 3,
    "Stuttgart": 4,
    "Mykonos": 2,
    "Madrid": 2,
    "Helsinki": 5,
    "Split": 3,
    "London": 5
}

# Constraints for specific events
friends_meeting_days_stuttgart = range(1, 5)  # Meeting a friend in Stuttgart between day 1 and day 4
conference_days_madrid = range(20, 22)          # Conference in Madrid (Day 20 and Day 21)

# Define direct flights between the cities
flights = {
    "Brussels": ["London", "Bucharest", "Madrid"],
    "Bucharest": ["London", "Brussels", "Madrid"],
    "Stuttgart": ["Split", "London"],
    "Mykonos": ["Madrid", "London"],
    "Madrid": ["Split", "Helsinki", "London", "Brussels", "Bucharest"],
    "Helsinki": ["London", "Split", "Madrid", "Brussels"],
    "Split": ["Madrid", "Helsinki", "Stuttgart", "London"],
    "London": ["Madrid", "Helsinki", "Brussels", "Bucharest", "Mykonos", "Stuttgart"]
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

# Meeting a friend in Stuttgart between day 1 and day 4
for day in friends_meeting_days_stuttgart:
    solver.add(trip[day - 1] == cities.index("Stuttgart"))  # Adjust for 0-based index

# Attend conference in Madrid on day 20 and day 21
for day in conference_days_madrid:
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