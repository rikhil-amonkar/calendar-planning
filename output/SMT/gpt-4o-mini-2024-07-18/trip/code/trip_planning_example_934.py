from z3 import *

# Define the number of days and cities
total_days = 17
cities = [
    "Brussels", "Rome", "Dubrovnik", 
    "Geneva", "Budapest", "Riga", "Valencia"
]

# Days assigned to each city with constraints
stay_duration = {
    "Brussels": 5,
    "Rome": 2,
    "Dubrovnik": 3,
    "Geneva": 5,
    "Budapest": 2,
    "Riga": 4,
    "Valencia": 2
}

# Constraints for specific events
workshop_days_brussels = range(7, 12)            # Workshop in Brussels (Day 7 to Day 11)
friends_meeting_days_riga = range(4, 8)          # Meeting friends in Riga (Day 4 to Day 7)
meeting_days_budapest = [16, 17]                  # Meeting a friend in Budapest (Day 16 to Day 17)

# Define direct flights between the cities
flights = {
    "Brussels": ["Valencia", "Geneva", "Riga", "Budapest", "Rome"],
    "Rome": ["Valencia", "Geneva", "Riga", "Budapest", "Brussels", "Dubrovnik"],
    "Dubrovnik": ["Geneva", "Rome"],
    "Geneva": ["Budapest", "Brussels", "Valencia", "Dubrovnik"],
    "Budapest": ["Geneva", "Rome", "Brussels"],
    "Riga": ["Brussels", "Rome"],
    "Valencia": ["Brussels", "Geneva", "Rome"]
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

# Workshop in Brussels between day 7 and day 11
for day in workshop_days_brussels:
    solver.add(trip[day - 1] == cities.index("Brussels"))  # Adjust for 0-based index

# Meeting friends in Riga between day 4 and day 7
for day in friends_meeting_days_riga:
    solver.add(trip[day - 1] == cities.index("Riga"))  # Adjust for 0-based index

# Meeting a friend in Budapest between day 16 and day 17
for day in meeting_days_budapest:
    solver.add(trip[day - 1] == cities.index("Budapest"))  # Adjust for 0-based index

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