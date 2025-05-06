from z3 import *

# Define the number of days and cities
total_days = 16
cities = [
    "Porto", "Prague", "Reykjavik",
    "Santorini", "Amsterdam", "Munich"
]

# Days assigned to each city with constraints
stay_duration = {
    "Porto": 5,
    "Prague": 4,
    "Reykjavik": 4,
    "Santorini": 2,
    "Amsterdam": 2,
    "Munich": 4
}

# Constraints for specific events
wedding_days_reykjavik = range(4, 8)     # Wedding in Reykjavik (Day 4 to Day 7)
conference_days_amsterdam = [14, 15]      # Conference in Amsterdam (Day 14 and Day 15)
friends_meeting_days_munich = range(7, 11) # Meet a friend in Munich (Day 7 to Day 10)

# Define direct flights between the cities
flights = {
    "Porto": ["Amsterdam", "Munich"],
    "Prague": ["Reykjavik", "Amsterdam", "Munich"],
    "Reykjavik": ["Amsterdam", "Prague", "Munich"],
    "Santorini": ["Amsterdam"],
    "Amsterdam": ["Porto", "Reykjavik", "Santorini", "Munich", "Prague"],
    "Munich": ["Amsterdam", "Porto", "Reykjavik", "Prague"]
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

# Attend wedding in Reykjavik between day 4 and day 7
for day in wedding_days_reykjavik:
    solver.add(trip[day - 1] == cities.index("Reykjavik"))  # Adjust for 0-based index

# Attend conference in Amsterdam on days 14 and 15
for day in conference_days_amsterdam:
    solver.add(trip[day - 1] == cities.index("Amsterdam"))  # Adjust for 0-based index

# Meet a friend in Munich between days 7 and 10
for day in friends_meeting_days_munich:
    solver.add(trip[day - 1] == cities.index("Munich"))  # Adjust for 0-based index

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