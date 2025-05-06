from z3 import *

# Define the number of days and cities
total_days = 10
cities = [
    "London", "Santorini", "Istanbul"
]

# Days assigned to each city with constraints
stay_duration = {
    "London": 3,
    "Santorini": 6,
    "Istanbul": 3
}

# Constraints for specific events
conference_days_santorini = [5, 10]  # Conferences in Santorini on day 5 and day 10

# Define direct flights between the cities
flights = {
    "Istanbul": ["London"],
    "London": ["Istanbul", "Santorini"],
    "Santorini": ["London"]
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for each day of the trip
trip = [Int(f'day_{i + 1}') for i in range(total_days)]

# Each day must refer to one of the cities
for day in trip:
    solver.add(Or([day == cities.index(city) for city in cities]))

# Count the days spent in each city
city_count = {city: Sum([If(trip[day] == cities.index(city), 1, 0) for day in range(total_days)]) for city in cities}

# Enforce stay durations
for city, duration in stay_duration.items():
    solver.add(city_count[city] == duration)

# Attend conferences in Santorini on days 5 and 10
for day in conference_days_santorini:
    solver.add(trip[day - 1] == cities.index("Santorini"))  # Adjust for 0-based index

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
    itinerary = []
    for day in range(total_days):
        city = cities[model[trip[day]].as_long()]
        itinerary.append(f"Day {day + 1}: {city}")
    print("\n".join(itinerary))
else:
    print("No valid trip plan found.")