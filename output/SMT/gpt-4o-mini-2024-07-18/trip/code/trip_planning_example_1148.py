from z3 import *

# Define the number of days and cities
total_days = 19
cities = [
    "Lisbon", "Dubrovnik", "Copenhagen",
    "Prague", "Tallinn", "Stockholm", 
    "Split", "Lyon"
]

# Days assigned to each city with constraints
stay_duration = {
    "Lisbon": 2,
    "Dubrovnik": 5,
    "Copenhagen": 5,
    "Prague": 3,
    "Tallinn": 2,
    "Stockholm": 4,
    "Split": 3,
    "Lyon": 2
}

# Constraints for specific events
workshop_days_lisbon = range(4, 6)  # Workshop in Lisbon (Day 4 to Day 5)
friends_meeting_days_tallinn = range(1, 3)  # Meet a friend in Tallinn (Day 1 to Day 2)
wedding_days_stockholm = range(13, 17)  # Wedding in Stockholm (Day 13 to Day 16)
annual_show_days_lyon = range(18, 20)    # Annual show in Lyon (Day 18 to Day 19)

# Define direct flights between the cities
flights = {
    "Dubrovnik": ["Stockholm", "Copenhagen"],
    "Lisbon": ["Copenhagen", "Lyon", "Stockholm"],
    "Copenhagen": ["Lisbon", "Stockholm", "Split", "Dubrovnik"],
    "Prague": ["Stockholm", "Lyon", "Lisbon", "Copenhagen", "Split", "Tallinn"],
    "Tallinn": ["Stockholm", "Copenhagen", "Prague"],
    "Stockholm": ["Dubrovnik", "Copenhagen", "Lisbon", "Prague", "Split"],
    "Split": ["Copenhagen", "Lyon", "Stockholm"],
    "Lyon": ["Lisbon", "Split", "Prague"]
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for each day of the trip
trip = [Int(f'day_{i + 1}') for i in range(total_days)]

# Each day must refer to one of the cities
for day in trip:
    solver.add(Or([day == cities.index(city) for city in cities]))

# Count the days spent in each city
city_count = {city: Sum([If(trip[day] == cities.index(city), 1, 0) for day in range(total_days)]) for city in cities}

# Enforce stay durations
for city, duration in stay_duration.items():
    solver.add(city_count[city] == duration)

# Attend workshop in Lisbon between day 4 and day 5
for day in workshop_days_lisbon:
    solver.add(trip[day - 1] == cities.index("Lisbon"))  # Adjust for 0-based index

# Meet a friend in Tallinn between day 1 and day 2
for day in friends_meeting_days_tallinn:
    solver.add(trip[day - 1] == cities.index("Tallinn"))  # Adjust for 0-based index

# Attend wedding in Stockholm between day 13 and day 16
for day in wedding_days_stockholm:
    solver.add(trip[day - 1] == cities.index("Stockholm"))  # Adjust for 0-based index

# Attend annual show in Lyon between day 18 and day 19
for day in annual_show_days_lyon:
    solver.add(trip[day - 1] == cities.index("Lyon"))  # Adjust for 0-based index

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