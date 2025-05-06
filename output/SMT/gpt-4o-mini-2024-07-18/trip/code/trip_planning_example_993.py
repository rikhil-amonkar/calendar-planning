from z3 import *

# Define the number of days and cities
total_days = 15
cities = [
    "Riga", "Frankfurt", "Amsterdam",
    "Vilnius", "London", "Stockholm", "Bucharest"
]

# Days assigned to each city with constraints
stay_duration = {
    "Riga": 2,
    "Frankfurt": 3,
    "Amsterdam": 2,
    "Vilnius": 5,
    "London": 2,
    "Stockholm": 3,
    "Bucharest": 4
}

# Constraints for specific events
meeting_days_amsterdam = [2, 3]             # Meeting a friend in Amsterdam (Day 2 to Day 3)
workshop_days_vilnius = range(7, 12)         # Workshop in Vilnius (Day 7 to Day 11)
wedding_days_stockholm = range(13, 16)       # Wedding in Stockholm (Day 13 to Day 15)

# Define direct flights between the cities
flights = {
    "London": ["Amsterdam", "Bucharest", "Frankfurt", "Stockholm"],
    "Riga": ["Vilnius", "Stockholm", "Frankfurt", "Bucharest"],
    "Frankfurt": ["Vilnius", "Stockholm", "Riga", "Amsterdam", "London"],
    "Amsterdam": ["London", "Bucharest", "Stockholm", "Frankfurt", "Vilnius", "Riga"],
    "Vilnius": ["Riga", "Frankfurt", "Amsterdam"],
    "Stockholm": ["Amsterdam", "Riga", "London"],
    "Bucharest": ["London", "Amsterdam", "Riga"]
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

# Meeting a friend in Amsterdam between day 2 and day 3
for day in meeting_days_amsterdam:
    solver.add(trip[day - 1] == cities.index("Amsterdam"))  # Adjust for 0-based index

# Workshop in Vilnius between day 7 and day 11
for day in workshop_days_vilnius:
    solver.add(trip[day - 1] == cities.index("Vilnius"))  # Adjust for 0-based index

# Wedding in Stockholm between day 13 and day 15
for day in wedding_days_stockholm:
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
    itinerary = []
    for day in range(total_days):
        city = cities[model[trip[day]].as_long()]
        itinerary.append(f"Day {day + 1}: {city}")
    print("\n".join(itinerary))
else:
    print("No valid trip plan found.")