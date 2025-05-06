from z3 import *

# Define the number of days and cities
total_days = 21
cities = [
    "Reykjavik", "Riga", "Warsaw",
    "Istanbul", "Krakow"
]

# Days assigned to each city with constraints
stay_duration = {
    "Reykjavik": 7,
    "Riga": 2,
    "Warsaw": 3,
    "Istanbul": 6,
    "Krakow": 7
}

# Constraints for specific events
friends_meeting_days_riga = range(1, 3)  # Meeting a friend in Riga (Day 1 to Day 2)
wedding_days_istanbul = range(2, 8)       # Wedding in Istanbul (Day 2 to Day 7)

# Define direct flights between the cities
flights = {
    "Reykjavik": ["Warsaw"],
    "Riga": ["Istanbul", "Warsaw"],
    "Warsaw": ["Istanbul", "Reykjavik", "Krakow", "Riga"],
    "Istanbul": ["Riga", "Warsaw", "Krakow"],
    "Krakow": ["Istanbul", "Warsaw"]
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

# Meeting a friend in Riga between day 1 and day 2
for day in friends_meeting_days_riga:
    solver.add(trip[day - 1] == cities.index("Riga"))  # Adjust for 0-based index

# Attend wedding in Istanbul between day 2 and day 7
for day in wedding_days_istanbul:
    solver.add(trip[day - 1] == cities.index("Istanbul"))  # Adjust for 0-based index

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