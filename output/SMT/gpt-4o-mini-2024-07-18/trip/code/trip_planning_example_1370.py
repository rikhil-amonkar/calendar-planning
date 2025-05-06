from z3 import *

# Define the number of days and the cities to visit
total_days = 30
cities = ["Santorini", "Krakow", "Paris", "Vilnius", "Munich", "Geneva", "Amsterdam", "Budapest", "Split"]

# Days assigned to each city with constraints
stay_duration = {
    "Santorini": 5,
    "Krakow": 5,
    "Paris": 5,
    "Vilnius": 3,
    "Munich": 5,
    "Geneva": 2,
    "Amsterdam": 4,
    "Budapest": 5,
    "Split": 4
}

# Constraints for specific events
friends_meeting_days_santorini = list(range(25, 30))  # Meet friends in Santorini (Day 25 to Day 29)
wedding_days_krakow = list(range(18, 23))              # Wedding in Krakow (Day 18 to Day 22)
friend_meeting_days_paris = list(range(11, 16))        # Meet friend in Paris (Day 11 to Day 15)

# Define direct flights between the cities
flights = {
    "Santorini": ["Geneva", "Amsterdam"],
    "Krakow": ["Vilnius", "Munich", "Split", "Paris", "Amsterdam"],
    "Paris": ["Krakow", "Amsterdam", "Split", "Geneva"],
    "Vilnius": ["Munich", "Krakow", "Amsterdam", "Paris", "Split"],
    "Munich": ["Vilnius", "Split", "Geneva", "Krakow", "Budapest", "Paris"],
    "Geneva": ["Santorini", "Amsterdam", "Budapest", "Munich", "Split"],
    "Amsterdam": ["Paris", "Budapest", "Munich", "Krakow", "Vilnius", "Geneva", "Split"],
    "Budapest": ["Amsterdam", "Geneva", "Paris", "Munich"],
    "Split": ["Krakow", "Munich", "Geneva", "Amsterdam", "Paris"],
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

# Friends meeting in Santorini between day 25 and day 29
for day in friends_meeting_days_santorini:
    solver.add(trip[day - 1] == cities.index("Santorini"))  # Adjust for 0-based index

# Wedding in Krakow between day 18 and day 22
for day in wedding_days_krakow:
    solver.add(trip[day - 1] == cities.index("Krakow"))  # Adjust for 0-based index

# Friends meeting in Paris between day 11 and day 15
for day in friend_meeting_days_paris:
    solver.add(trip[day - 1] == cities.index("Paris"))  # Adjust for 0-based index

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
    for day in range(total_days):
        print(f"Day {day + 1}: {cities[model[trip[day]].as_long()]}")
else:
    print("No valid trip plan found.")