from z3 import *

# Define the number of days and cities
total_days = 16
cities = [
    "Vienna", "Barcelona", "Edinburgh", 
    "Krakow", "Riga", "Hamburg", 
    "Paris", "Stockholm"
]

# Days assigned to each city with constraints
stay_duration = {
    "Vienna": 4,
    "Barcelona": 2,
    "Edinburgh": 4,
    "Krakow": 3,
    "Riga": 4,
    "Hamburg": 2,
    "Paris": 2,
    "Stockholm": 2
}

# Constraints for specific events
conference_days_hamburg = [10, 11]  # Conference in Hamburg (Day 10 and Day 11)
wedding_days_paris = [1, 2]          # Wedding in Paris (Day 1 and Day 2)
friends_meeting_days_edinburgh = range(12, 16)  # Meeting friend in Edinburgh (Day 12 to Day 15)
relatives_visit_days_stockholm = [15, 16]  # Visit relatives in Stockholm (Day 15 and Day 16)

# Define direct flights between the cities
flights = {
    "Hamburg": ["Stockholm", "Vienna", "Barcelona", "Edinburgh"],
    "Vienna": ["Stockholm", "Edinburgh", "Hamburg", "Barcelona", "Krakow", "Riga"],
    "Barcelona": ["Riga", "Hamburg", "Stockholm", "Krakow", "Edinburgh"],
    "Edinburgh": ["Paris", "Stockholm", "Hamburg", "Krakow", "Vienna"],
    "Krakow": ["Barcelona", "Riga", "Vienna", "Edinburgh", "Paris", "Stockholm"],
    "Riga": ["Edinburgh", "Barcelona", "Hamburg", "Stockholm", "Vienna"],
    "Paris": ["Edinburgh", "Krakow", "Barcelona", "Stockholm"],
    "Stockholm": ["Hamburg", "Vienna", "Riga", "Barcelona", "Edinburgh"]
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

# Conference in Hamburg between day 10 and day 11
for day in conference_days_hamburg:
    solver.add(trip[day - 1] == cities.index("Hamburg"))  # Adjust for 0-based index

# Wedding in Paris between day 1 and day 2
for day in wedding_days_paris:
    solver.add(trip[day - 1] == cities.index("Paris"))  # Adjust for 0-based index

# Meeting friends in Edinburgh between day 12 and day 15
for day in friends_meeting_days_edinburgh:
    solver.add(trip[day - 1] == cities.index("Edinburgh"))  # Adjust for 0-based index

# Visiting relatives in Stockholm between day 15 and day 16
for day in relatives_visit_days_stockholm:
    solver.add(trip[day - 1] == cities.index("Stockholm"))  # Adjust for 0-based index

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