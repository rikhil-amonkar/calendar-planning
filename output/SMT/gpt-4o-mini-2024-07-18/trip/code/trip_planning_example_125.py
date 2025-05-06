from z3 import *

# Define the number of days and cities
total_days = 15
cities = [
    "Stuttgart", "Seville", "Manchester"
]

# Days assigned to each city with constraints
stay_duration = {
    "Stuttgart": 6,
    "Seville": 7,
    "Manchester": 4
}

# Constraints for specific events
friends_meeting_days_stuttgart = range(1, 7)  # Meeting a friend in Stuttgart between day 1 and day 6

# Define direct flights between the cities
flights = {
    "Manchester": ["Seville", "Stuttgart"],
    "Stuttgart": ["Manchester"],
    "Seville": ["Manchester"]
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

# Meeting friends in Stuttgart between day 1 and day 6
for day in friends_meeting_days_stuttgart:
    solver.add(trip[day - 1] == cities.index("Stuttgart"))  # Adjust for 0-based index

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