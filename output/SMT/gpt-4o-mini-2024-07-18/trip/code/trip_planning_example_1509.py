from z3 import *

# Define the number of days and cities
total_days = 25
cities = [
    "Paris", "Warsaw", "Krakow", "Tallinn", "Riga",
    "Copenhagen", "Helsinki", "Oslo", "Santorini", "Lyon"
]

# Days assigned to each city with constraints
stay_duration = {
    "Paris": 5,
    "Warsaw": 2,
    "Krakow": 2,
    "Tallinn": 2,
    "Riga": 2,
    "Copenhagen": 5,
    "Helsinki": 5,
    "Oslo": 5,
    "Santorini": 2,
    "Lyon": 4
}

# Constraints for specific events
friends_meeting_days_paris = range(4, 9)      # Meeting friends in Paris (Day 4 to Day 8)
workshop_days_krakow = range(17, 19)            # Workshop in Krakow (Day 17 and Day 18)
wedding_days_riga = range(23, 25)               # Wedding in Riga (Day 23 and Day 24)
meeting_friends_helsinki = range(18, 23)        # Meeting a friend in Helsinki (Day 18 to Day 22)
relatives_visit_santorini = [12, 13]            # Visiting relatives in Santorini (Day 12 and Day 13)

# Define direct flights between the cities
flights = {
    "Warsaw": ["Riga", "Tallinn", "Copenhagen"],
    "Krakow": ["Warsaw", "Helsinki"],
    "Tallinn": ["Warsaw", "Riga", "Helsinki"],
    "Riga": ["Warsaw", "Tallinn", "Paris"],
    "Copenhagen": ["Helsinki", "Krakow", "Riga", "Warsaw"],
    "Helsinki": ["Copenhagen", "Krakow", "Riga", "Oslo"],
    "Oslo": ["Paris", "Lyon", "Tallinn", "Helsinki", "Riga", "Copenhagen", "Warsaw"],
    "Santorini": ["Copenhagen", "Oslo"],
    "Lyon": ["Paris", "Oslo"],
    "Paris": ["Oslo", "Riga", "Copenhagen", "Warsaw", "Krakow", "Tallinn", "Helsinki"]
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

# Meeting friends in Paris between day 4 and day 8
for day in friends_meeting_days_paris:
    solver.add(trip[day - 1] == cities.index("Paris"))  # Adjust for 0-based index

# Attend workshop in Krakow between day 17 and day 18
for day in workshop_days_krakow:
    solver.add(trip[day - 1] == cities.index("Krakow"))  # Adjust for 0-based index

# Attend wedding in Riga between day 23 and day 24
for day in wedding_days_riga:
    solver.add(trip[day - 1] == cities.index("Riga"))  # Adjust for 0-based index

# Meeting a friend in Helsinki between day 18 and day 22
for day in meeting_friends_helsinki:
    solver.add(trip[day - 1] == cities.index("Helsinki"))  # Adjust for 0-based index

# Visit relatives in Santorini on days 12 and 13
for day in relatives_visit_santorini:
    solver.add(trip[day - 1] == cities.index("Santorini"))  # Adjust for 0-based index

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