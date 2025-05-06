from z3 import *

# Define constants
total_days = 20
cities = [
    "Paris", "Florence", "Vienna", 
    "Porto", "Munich", "Nice", 
    "Warsaw"
]

# Days assigned to each city with constraints
stay_duration = {
    "Paris": 5,
    "Florence": 3,
    "Vienna": 2,
    "Porto": 3,
    "Munich": 5,
    "Nice": 5,
    "Warsaw": 3
}

# Constraints for specific events
relatives_visit_days_vienna = range(19, 21)   # Days 19 and 20 in Vienna
workshop_days_porto = range(1, 4)              # Days 1 to 3 in Porto
wedding_days_warsaw = range(13, 16)            # Wedding in Warsaw between days 13 and 15

# Define direct flights between the cities
flights = {
    "Florence": ["Vienna", "Munich", "Paris"],
    "Paris": ["Warsaw", "Florence", "Vienna", "Nice", "Munich", "Porto"],
    "Vienna": ["Florence", "Munich", "Porto", "Warsaw", "Nice"],
    "Porto": ["Vienna", "Munich", "Nice", "Paris", "Warsaw"],
    "Munich": ["Vienna", "Florence", "Warsaw", "Nice", "Porto", "Paris"],
    "Nice": ["Vienna", "Munich", "Paris", "Warsaw", "Porto"],
    "Warsaw": ["Vienna", "Paris", "Munich", "Nice", "Porto"]
}

# Initialize the Z3 solver
solver = Solver()

# Create a variable for each day of the trip
trip = [Int(f'day_{i + 1}') for i in range(total_days)]

# Each day must refer to one of the cities
for day in trip:
    solver.add(Or([day == cities.index(city) for city in cities]))

# Count the days spent in each city
city_count = {city: Sum([If(trip[day] == cities.index(city), 1, 0) for day in range(total_days)]) for city in cities}

# Enforce stay durations
for city, duration in stay_duration.items():
    solver.add(city_count[city] == duration)

# Visit relatives in Vienna on days 19 and 20
for day in relatives_visit_days_vienna:
    solver.add(trip[day - 1] == cities.index("Vienna"))  # Adjust for 0-based index

# Attend workshop in Porto on days 1 to 3
for day in workshop_days_porto:
    solver.add(trip[day - 1] == cities.index("Porto"))  # Adjust for 0-based index

# Attend wedding in Warsaw between days 13 and 15
for day in wedding_days_warsaw:
    solver.add(trip[day - 1] == cities.index("Warsaw"))  # Adjust for 0-based index

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