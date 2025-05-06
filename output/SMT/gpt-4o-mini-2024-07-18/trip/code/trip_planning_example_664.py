from z3 import *

# Define the number of days and cities
total_days = 18
cities = [
    "Tallinn", "Bucharest", "Seville", 
    "Stockholm", "Munich", "Milan"
]

# Days assigned to each city with constraints
stay_duration = {
    "Tallinn": 2,
    "Bucharest": 4,
    "Seville": 5,
    "Stockholm": 5,
    "Munich": 5,
    "Milan": 2
}

# Constraints for specific events
relatives_visit_days_bucharest = range(1, 5)  # Visiting relatives in Bucharest (Day 1 to Day 4)
friends_meeting_days_seville = range(8, 13)    # Meeting friends in Seville (Day 8 to Day 12)
wedding_days_munich = range(4, 9)               # Wedding in Munich (Day 4 to Day 8)

# Define direct flights between the cities
flights = {
    "Tallinn": ["Stockholm", "Munich"],
    "Bucharest": ["Munich"],
    "Seville": ["Milan", "Munich"],
    "Stockholm": ["Tallinn", "Milan", "Munich"],
    "Munich": ["Bucharest", "Seville", "Stockholm", "Milan", "Tallinn"],
    "Milan": ["Stockholm", "Seville", "Munich"]
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

# Visiting relatives in Bucharest between day 1 and day 4
for day in relatives_visit_days_bucharest:
    solver.add(trip[day - 1] == cities.index("Bucharest"))  # Adjust for 0-based index

# Meeting friends in Seville between day 8 and day 12
for day in friends_meeting_days_seville:
    solver.add(trip[day - 1] == cities.index("Seville"))  # Adjust for 0-based index

# Wedding in Munich between day 4 and day 8
for day in wedding_days_munich:
    solver.add(trip[day - 1] == cities.index("Munich"))  # Adjust for 0-based index

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