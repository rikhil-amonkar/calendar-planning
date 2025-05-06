from z3 import *

# Define the number of days and cities
total_days = 21
cities = ["Oslo", "Stuttgart", "Reykjavik", "Split", "Geneva", "Porto", "Tallinn", "Stockholm"]

# Days assigned to each city with constraints
stay_duration = {
    "Oslo": 5,
    "Stuttgart": 5,
    "Reykjavik": 2,
    "Split": 3,
    "Geneva": 2,
    "Porto": 3,
    "Tallinn": 5,
    "Stockholm": 3
}

# Constraints for specific events
conference_days = [1, 2]  # Reykjavik
workshop_days = [19, 20, 21]  # Porto
friend_meeting_days = [2, 3, 4]  # Stockholm

# Define direct flights between the cities
flights = {
    "Reykjavik": ["Stuttgart", "Stockholm", "Tallinn", "Oslo"],
    "Stuttgart": ["Porto", "Stockholm"],
    "Oslo": ["Split", "Geneva", "Porto", "Stuttgart"],
    "Split": ["Stuttgart", "Stockholm"],
    "Tallinn": ["Oslo"],
    "Stockholm": ["Geneva", "Split", "Oslo"],
    "Geneva": ["Porto", "Split"],
    "Porto": []
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for each day
# trip[day] will indicate the city to be visited on that day
trip = [Int(f'day_{i + 1}') for i in range(total_days)]

# Each day must refer to one of the cities
for day in trip:
    solver.add(Or([day == cities.index(city) for city in cities]))

# Constraint for city stays
# Create a dictionary to count days spent in each city
city_count = {city: Sum([If(trip[day] == cities.index(city), 1, 0) for day in range(total_days)]) for city in cities}

# Enforce stay durations
for city, duration in stay_duration.items():
    solver.add(city_count[city] == duration)

# Conference in Reykjavik on Day 1 and Day 2
solver.add(trip[0] == cities.index("Reykjavik"))
solver.add(trip[1] == cities.index("Reykjavik"))

# Workshop in Porto between Day 19 and Day 21
solver.add(And(trip[18] == cities.index("Porto"), trip[19] == cities.index("Porto"), trip[20] == cities.index("Porto")))

# Meeting a friend in Stockholm between Day 2 and Day 4
for day in range(2, 5):
    solver.add(trip[day] == cities.index("Stockholm"))

# Define direct flight connections
for day in range(total_days - 1):
    curr_city = trip[day]
    next_city = trip[day + 1]
    # If transitioning from one city to another, it must be a valid flight
    solver.add(Or([And(curr_city == cities.index(city), next_city == cities.index(next_city_city)) for city in cities for next_city_city in flights[cities[city]]]))

# All variables must be the same city count for trips
if solver.check() == sat:
    model = solver.model()
    for day in range(total_days):
        print(f"Day {day + 1}: {cities[model[trip[day]].as_long()]}")
else:
    print("No valid trip plan found.")