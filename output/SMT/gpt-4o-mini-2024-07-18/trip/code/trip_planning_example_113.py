from z3 import *

# Define the number of days and cities
total_days = 12
cities = [
    "Naples", "Seville", "Milan"
]

# Days assigned to each city with constraints
stay_duration = {
    "Naples": 3,
    "Seville": 4,
    "Milan": 7
}

# Constraints for specific events
annual_show_seville = range(9, 13)  # Annual show in Seville from day 9 to day 12

# Define direct flights between the cities
flights = {
    "Milan": ["Seville", "Naples"],
    "Seville": ["Milan"],
    "Naples": ["Milan"]
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

# Attend annual show in Seville between day 9 and day 12
for day in annual_show_seville:
    solver.add(trip[day - 1] == cities.index("Seville"))  # Adjust for 0-based index

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