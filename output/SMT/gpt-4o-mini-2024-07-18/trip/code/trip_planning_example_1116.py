from z3 import *

# Define the number of days and cities
total_days = 20
cities = ["Oslo", "Reykjavik", "Stockholm", "Munich", "Frankfurt", "Barcelona", "Bucharest", "Split"]

# Days assigned to each city with constraints
stay_duration = {
    "Oslo": 2,
    "Reykjavik": 5,
    "Stockholm": 4,
    "Munich": 4,
    "Frankfurt": 4,
    "Barcelona": 3,
    "Bucharest": 2,
    "Split": 3
}

# Constraints for specific events
annual_show_days_oslo = [16, 17]  # Annual show in Oslo (Day 16 to Day 17)
friend_meeting_days_reykjavik = range(9, 14)  # Meet friend in Reykjavik (Day 9 to Day 13)
relatives_visit_days_munich = range(13, 16)    # Visit relatives in Munich (Day 13 to Day 16)
workshop_days_frankfurt = range(17, 21)         # Workshop in Frankfurt (Day 17 to Day 20)

# Define direct flights between the cities
flights = {
    "Reykjavik": ["Munich", "Oslo", "Frankfurt"],
    "Oslo": ["Reykjavik", "Frankfurt", "Split", "Stockholm"],
    "Stockholm": ["Reykjavik", "Barcelona", "Munich", "Frankfurt", "Split"],
    "Munich": ["Reykjavik", "Frankfurt", "Oslo", "Bucharest", "Split", "Barcelona"],
    "Frankfurt": ["Munich", "Oslo", "Barcelona", "Bucharest"],
    "Barcelona": ["Bucharest", "Frankfurt", "Stockholm", "Reykjavik"],
    "Bucharest": ["Munich", "Barcelona", "Oslo", "Frankfurt"],
    "Split": ["Oslo", "Stockholm", "Munich", "Barcelona"],
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

# Annual show in Oslo during day 16 and day 17
for day in annual_show_days_oslo:
    solver.add(trip[day - 1] == cities.index("Oslo"))  # Adjust for 0-based index

# Meeting friends in Reykjavik between day 9 and day 13
for day in friend_meeting_days_reykjavik:
    solver.add(trip[day - 1] == cities.index("Reykjavik"))  # Adjust for 0-based index

# Visit relatives in Munich between day 13 and day 16
for day in relatives_visit_days_munich:
    solver.add(trip[day - 1] == cities.index("Munich"))  # Adjust for 0-based index

# Workshop in Frankfurt from day 17 to day 20
for day in workshop_days_frankfurt:
    solver.add(trip[day - 1] == cities.index("Frankfurt"))  # Adjust for 0-based index

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