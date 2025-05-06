from z3 import *

# Define constants
total_days = 17
cities = [
    "Venice", "London", "Lisbon", 
    "Brussels", "Reykjavik", "Santorini", 
    "Madrid"
]

# Days assigned to each city with constraints
stay_duration = {
    "Venice": 3,
    "London": 3,
    "Lisbon": 4,
    "Brussels": 2,
    "Reykjavik": 3,
    "Santorini": 3,
    "Madrid": 5
}

# Constraints for specific events
relatives_visit_days_venice = range(5, 8)  # Days 5 to 7 in Venice
conference_days_brussels = [1, 2]           # Conference in Brussels on days 1 and 2
wedding_days_madrid = range(7, 12)          # Wedding in Madrid between days 7 and 11

# Define direct flights between the cities
flights = {
    "Venice": ["Madrid", "Brussels", "Santorini", "Lisbon", "London"],
    "London": ["Brussels", "Lisbon", "Reykjavik", "Madrid", "Santorini", "Venice"],
    "Lisbon": ["Reykjavik", "Venice", "London", "Brussels", "Madrid"],
    "Brussels": ["Venice", "London", "Lisbon", "Reykjavik", "Madrid"],
    "Reykjavik": ["Lisbon", "London", "Madrid"],
    "Santorini": ["London", "Madrid", "Venice"],
    "Madrid": ["Venice", "London", "Lisbon", "Reykjavik", "Santorini", "Brussels"]
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

# Attend conference in Brussels on days 1 and 2
for day in conference_days_brussels:
    solver.add(trip[day - 1] == cities.index("Brussels"))  # Adjust for 0-based index

# Visit relatives in Venice on days 5 to 7
for day in relatives_visit_days_venice:
    solver.add(trip[day - 1] == cities.index("Venice"))  # Adjust for 0-based index

# Attend wedding in Madrid between days 7 and 11
for day in wedding_days_madrid:
    solver.add(trip[day - 1] == cities.index("Madrid"))  # Adjust for 0-based index

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