from z3 import *

# Define constants
total_days = 15
cities = [
    "Vienna", "Milan", "Rome", 
    "Riga", "Lisbon", "Vilnius", 
    "Oslo"
]

# Days assigned to each city with constraints
stay_duration = {
    "Vienna": 4,
    "Milan": 2,
    "Rome": 3,
    "Riga": 2,
    "Lisbon": 3,
    "Vilnius": 4,
    "Oslo": 3
}

# Constraints for specific events
conference_days_vienna = [1, 4]       # Conference in Vienna on days 1 and 4
relatives_visit_days_lisbon = range(11, 13)  # Visit relatives in Lisbon (Day 11 and 12)
friends_meeting_days_oslo = range(13, 15)    # Meet friends in Oslo (Day 13 and 14)

# Define direct flights between the cities
flights = {
    "Vienna": ["Milan", "Vilnius", "Lisbon", "Riga", "Rome", "Oslo"],
    "Milan": ["Vienna", "Oslo", "Rome", "Riga", "Lisbon"],
    "Rome": ["Oslo", "Riga", "Lisbon", "Vienna"],
    "Riga": ["Oslo", "Milan", "Lisbon", "Vilnius"],
    "Lisbon": ["Oslo", "Milan", "Riga", "Vienna"],
    "Vilnius": ["Oslo", "Riga", "Vienna", "Milan"],
    "Oslo": ["Vienna", "Milan", "Rome", "Riga", "Lisbon", "Vilnius"]
}

# Initialize the Z3 solver
solver = Solver()

# Create a variable for each day of the trip
trip = [Int(f'day_{i + 1}') for i in range(total_days)]

# Each day must refer to one of the cities
for day in trip:
    solver.add(Or([day == cities.index(city) for city in cities]))

# Count the days spent in each city
city_count = {city: Sum([If(trip[day] == cities.index(city), 1, 0) for day in range(total_days)]) for city in cities}

# Enforce stay durations
for city, duration in stay_duration.items():
    solver.add(city_count[city] == duration)

# Attend conference in Vienna on days 1 and 4
for day in conference_days_vienna:
    solver.add(trip[day - 1] == cities.index("Vienna"))  # Adjust for 0-based index

# Visit relatives in Lisbon on days 11 and 12
for day in relatives_visit_days_lisbon:
    solver.add(trip[day - 1] == cities.index("Lisbon"))  # Adjust for 0-based index

# Meet friends in Oslo between days 13 and 14
for day in friends_meeting_days_oslo:
    solver.add(trip[day - 1] == cities.index("Oslo"))  # Adjust for 0-based index

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