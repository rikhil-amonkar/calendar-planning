from z3 import *

# Define the number of days and cities
total_days = 18
cities = [
    "Helsinki", "Valencia", "Dubrovnik",
    "Porto", "Prague", "Reykjavik"
]

# Days assigned to each city with constraints
stay_duration = {
    "Helsinki": 4,
    "Valencia": 5,
    "Dubrovnik": 4,
    "Porto": 3,
    "Prague": 3,
    "Reykjavik": 4
}

# Constraints for specific events
friend_meeting_days_porto = range(16, 18)  # Meet friend in Porto (Day 16 to 17)

# Define direct flights between the cities
flights = {
    "Helsinki": ["Prague", "Reykjavik", "Dubrovnik"],
    "Prague": ["Helsinki", "Valencia"],
    "Valencia": ["Prague", "Porto"],
    "Porto": ["Valencia"],
    "Dubrovnik": ["Helsinki"],
    "Reykjavik": ["Helsinki", "Prague"]
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

# Meet friends in Porto between day 16 and day 18
for day in friend_meeting_days_porto:
    solver.add(trip[day - 1] == cities.index("Porto"))  # Adjust for 0-based index

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