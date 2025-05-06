from z3 import *

# Define constants
total_days = 16
cities = [
    "Frankfurt", "Manchester", "Valencia", 
    "Naples", "Oslo", "Vilnius"
]

# Days assigned to each city with constraints
stay_duration = {
    "Frankfurt": 4,
    "Manchester": 4,
    "Valencia": 4,
    "Naples": 4,
    "Oslo": 3,
    "Vilnius": 2
}

# Constraints for specific events
annual_show_days_frankfurt = range(13, 17)  # Days 13 to 16 in Frankfurt
wedding_days_vilnius = [12]                    # Wedding on day 12 in Vilnius

# Define direct flights between the cities
flights = {
    "Frankfurt": ["Valencia", "Manchester", "Naples", "Oslo", "Vilnius"],
    "Manchester": ["Frankfurt", "Naples", "Oslo"],
    "Valencia": ["Frankfurt", "Naples"],
    "Naples": ["Frankfurt", "Manchester", "Oslo", "Valencia"],
    "Oslo": ["Frankfurt", "Vilnius", "Manchester", "Naples"],
    "Vilnius": ["Frankfurt", "Oslo"]
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

# Attend annual show in Frankfurt between days 13 and 16
for day in annual_show_days_frankfurt:
    solver.add(trip[day - 1] == cities.index("Frankfurt"))  # Adjust for 0-based index

# Attend wedding in Vilnius on day 12
solver.add(trip[11] == cities.index("Vilnius"))  # Day 12 (adjust for 0-based index)

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