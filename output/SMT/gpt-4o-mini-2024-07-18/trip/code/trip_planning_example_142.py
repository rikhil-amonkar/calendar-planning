from z3 import *

# Define the number of days and cities
total_days = 7
cities = [
    "Madrid", "Dublin", "Tallinn"
]

# Days assigned to each city with constraints
stay_duration = {
    "Madrid": 4,
    "Dublin": 3,
    "Tallinn": 2
}

# Constraints for specific events
workshop_days_tallinn = range(6, 8)  # Days 6 and 7 in Tallinn

# Define direct flights between the cities
flights = {
    "Madrid": ["Dublin"],
    "Dublin": ["Madrid", "Tallinn"],
    "Tallinn": ["Dublin"]
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

# Attend workshop in Tallinn between days 6 and 7
for day in workshop_days_tallinn:
    solver.add(trip[day - 1] == cities.index("Tallinn"))  # Adjust for 0-based index

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