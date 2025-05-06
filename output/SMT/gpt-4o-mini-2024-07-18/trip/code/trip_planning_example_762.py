from z3 import *

# Define the number of days and cities
total_days = 13
cities = ["Dublin", "Madrid", "Oslo", "London", "Vilnius", "Berlin"]

# Days assigned to each city with constraints
stay_duration = {
    "Dublin": 3,
    "Madrid": 2,
    "Oslo": 3,
    "London": 2,
    "Vilnius": 3,
    "Berlin": 5
}

# Constraints for specific events
friends_meeting_days_dublin = range(7, 10)  # Meet friends in Dublin (Day 7 to Day 9)
relatives_visit_days_madrid = range(2, 4)    # Visit relatives in Madrid (Day 2 to Day 3)
wedding_days_berlin = range(3, 8)             # Wedding in Berlin (Day 3 to Day 7)

# Define direct flights between the cities
flights = {
    "Dublin": ["Madrid", "Oslo", "London", "Berlin"],
    "Madrid": ["Oslo", "Dublin", "London", "Berlin"],
    "Oslo": ["Vilnius", "Berlin", "London", "Dublin", "Madrid"],
    "London": ["Dublin", "Madrid", "Oslo", "Berlin"],
    "Vilnius": ["Oslo", "Berlin"],
    "Berlin": ["Vilnius", "Madrid", "Oslo", "London", "Dublin"]
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

# Meeting friends in Dublin between day 7 and day 9
for day in friends_meeting_days_dublin:
    solver.add(trip[day - 1] == cities.index("Dublin"))  # Adjust for 0-based index

# Visiting relatives in Madrid between day 2 and day 3
for day in relatives_visit_days_madrid:
    solver.add(trip[day - 1] == cities.index("Madrid"))  # Adjust for 0-based index

# Wedding in Berlin from day 3 to day 7
for day in wedding_days_berlin:
    solver.add(trip[day - 1] == cities.index("Berlin"))  # Adjust for 0-based index

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