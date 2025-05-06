from z3 import *

# Define the number of days and cities
total_days = 27
cities = [
    "Santorini", "Valencia", "Madrid",
    "Seville", "Bucharest", "Vienna",
    "Riga", "Tallinn", "Krakow", "Frankfurt"
]

# Days assigned to each city with constraints
stay_duration = {
    "Santorini": 3,
    "Valencia": 4,
    "Madrid": 2,
    "Seville": 2,
    "Bucharest": 3,
    "Vienna": 4,
    "Riga": 4,
    "Tallinn": 5,
    "Krakow": 5,
    "Frankfurt": 4
}

# Constraints for specific events
annual_show_days_madrid = range(6, 8)  # Annual show in Madrid (Day 6 and Day 7)
wedding_days_vienna = range(3, 7)       # Wedding in Vienna (Day 3 to Day 6)
friends_meeting_days_krakow = range(11, 16)  # Friends meeting in Krakow (Day 11 to Day 15)
conference_days_riga = [20, 23]          # Conference in Riga (Day 20 and Day 23)
workshop_days_tallinn = range(23, 28)    # Workshop in Tallinn (Day 23 to Day 27)

# Define direct flights between the cities
flights = {
    "Vienna": ["Bucharest", "Seville", "Valencia", "Madrid", "Riga", "Krakow", "Frankfurt"],
    "Santorini": ["Madrid", "Bucharest", "Vienna"],
    "Valencia": ["Seville", "Bucharest", "Madrid", "Krakow", "Frankfurt"],
    "Madrid": ["Valencia", "Seville", "Bucharest", "Vienna", "Frankfurt"],
    "Seville": ["Valencia", "Vienna", "Madrid"],
    "Bucharest": ["Vienna", "Riga", "Valencia", "Santorini", "Madrid"],
    "Riga": ["Bucharest", "Vienna", "Tallinn"],
    "Tallinn": ["Riga", "Frankfurt"],
    "Krakow": ["Frankfurt", "Vienna", "Valencia"],
    "Frankfurt": ["Vienna", "Krakow", "Tallinn", "Riga", "Madrid"]
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

# Annual show in Madrid between day 6 and day 7
for day in annual_show_days_madrid:
    solver.add(trip[day - 1] == cities.index("Madrid"))  # Adjust for 0-based index

# Wedding in Vienna between day 3 and day 6
for day in wedding_days_vienna:
    solver.add(trip[day - 1] == cities.index("Vienna"))  # Adjust for 0-based index

# Meeting friends in Krakow between day 11 and day 15
for day in friends_meeting_days_krakow:
    solver.add(trip[day - 1] == cities.index("Krakow"))  # Adjust for 0-based index

# Conference in Riga on day 20 and day 23
for day in conference_days_riga:
    solver.add(trip[day - 1] == cities.index("Riga"))  # Adjust for 0-based index

# Workshop in Tallinn between day 23 and day 27
for day in workshop_days_tallinn:
    solver.add(trip[day - 1] == cities.index("Tallinn"))  # Adjust for 0-based index

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