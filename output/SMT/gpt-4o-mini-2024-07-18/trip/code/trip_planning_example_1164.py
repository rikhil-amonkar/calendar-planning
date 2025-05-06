from z3 import *

# Define the number of days and cities
total_days = 17
cities = [
    "Reykjavik", "Stockholm", "Porto", 
    "Nice", "Venice", "Vienna", 
    "Split", "Copenhagen"
]

# Days assigned to each city with constraints
stay_duration = {
    "Reykjavik": 2,
    "Stockholm": 2,
    "Porto": 5,
    "Nice": 3,
    "Venice": 4,
    "Vienna": 3,
    "Split": 3,
    "Copenhagen": 2
}

# Constraints for specific events
meet_friends_reykjavik = range(3, 5)  # Meet friends in Reykjavik (Day 3 to Day 4)
meet_friends_stockholm = range(4, 6)  # Meet friends in Stockholm (Day 4 to Day 5)
wedding_days_porto = range(13, 18)     # Wedding in Porto (Day 13 to Day 17)
workshop_days_vienna = range(11, 13)   # Workshop in Vienna (Day 11 to Day 13)

# Define direct flights between the cities
flights = {
    "Copenhagen": ["Vienna", "Split"],
    "Nice": ["Stockholm", "Reykjavik", "Venice", "Porto", "Copenhagen"],
    "Split": ["Copenhagen", "Vienna", "Stockholm"],
    "Reykjavik": ["Vienna", "Copenhagen", "Stockholm"],
    "Stockholm": ["Nice", "Copenhagen", "Vienna"],
    "Venice": ["Nice", "Vienna"],
    "Vienna": ["Copenhagen", "Porto", "Reykjavik", "Stockholm"],
    "Porto": ["Nice", "Copenhagen", "Vienna"]
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

# Meet friends in Reykjavik between day 3 and day 4
for day in meet_friends_reykjavik:
    solver.add(trip[day - 1] == cities.index("Reykjavik"))  # Adjust for 0-based index

# Meet friends in Stockholm between day 4 and day 5
for day in meet_friends_stockholm:
    solver.add(trip[day - 1] == cities.index("Stockholm"))  # Adjust for 0-based index

# Attend wedding in Porto between day 13 and day 17
for day in wedding_days_porto:
    solver.add(trip[day - 1] == cities.index("Porto"))  # Adjust for 0-based index

# Attend workshop in Vienna between day 11 and day 13
for day in workshop_days_vienna:
    solver.add(trip[day - 1] == cities.index("Vienna"))  # Adjust for 0-based index

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