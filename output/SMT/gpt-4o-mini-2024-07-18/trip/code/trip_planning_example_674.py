from z3 import *

# Define the number of days and cities
total_days = 14
cities = [
    "Helsinki", "Warsaw", "Madrid", 
    "Split", "Reykjavik", "Budapest"
]

# Days assigned to each city with constraints
stay_duration = {
    "Helsinki": 2,
    "Warsaw": 3,
    "Madrid": 4,
    "Split": 4,
    "Reykjavik": 2,
    "Budapest": 4
}

# Constraints for specific events
workshop_days_helsinki = range(1, 3)    # Attend workshop in Helsinki between day 1 and day 2
relatives_visit_days_warsaw = range(9, 12)  # Visit relatives in Warsaw between day 9 and day 11
friends_meeting_days_reykjavik = range(8, 10) # Meeting friends in Reykjavik

# Define direct flights between the cities
flights = {
    "Helsinki": ["Reykjavik", "Split", "Madrid", "Budapest", "Warsaw"],
    "Warsaw": ["Budapest", "Split", "Madrid", "Reykjavik"],
    "Madrid": ["Split", "Budapest", "Warsaw"],
    "Split": ["Madrid", "Warsaw"],
    "Reykjavik": ["Helsinki", "Warsaw", "Budapest"],
    "Budapest": ["Helsinki", "Warsaw", "Madrid", "Reykjavik"]
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

# Attend workshop in Helsinki between day 1 and day 2
for day in workshop_days_helsinki:
    solver.add(trip[day - 1] == cities.index("Helsinki"))  # Adjust for 0-based index

# Visit relatives in Warsaw between day 9 and day 11
for day in relatives_visit_days_warsaw:
    solver.add(trip[day - 1] == cities.index("Warsaw"))  # Adjust for 0-based index

# Meet a friend in Reykjavik between day 8 and day 9
for day in friends_meeting_days_reykjavik:
    solver.add(trip[day - 1] == cities.index("Reykjavik"))  # Adjust for 0-based index

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