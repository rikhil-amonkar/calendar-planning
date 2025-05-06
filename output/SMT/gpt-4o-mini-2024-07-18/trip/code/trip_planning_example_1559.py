from z3 import *

# Define the number of days and cities
total_days = 25
cities = [
    "Valencia", "Oslo", "Lyon", 
    "Prague", "Paris", "Nice", 
    "Seville", "Tallinn", "Mykonos", "Lisbon"
]

# Days assigned to each city with constraints
stay_duration = {
    "Valencia": 2,
    "Oslo": 3,
    "Lyon": 4,
    "Prague": 3,
    "Paris": 4,
    "Nice": 4,
    "Seville": 5,
    "Tallinn": 2,
    "Mykonos": 5,
    "Lisbon": 2
}

# Constraints for specific events
friends_meeting_days_valencia = [3, 4]       # Meeting friends in Valencia (Day 3 to Day 4)
friends_meeting_days_oslo = range(13, 16)     # Meeting a friend in Oslo (Day 13 to Day 15)
annual_show_days_seville = range(5, 10)       # Annual show in Seville (Day 5 to Day 9)
wedding_days_mykonos = range(21, 26)           # Wedding in Mykonos (Day 21 to Day 25)

# Define direct flights between the cities
flights = {
    "Lisbon": ["Paris", "Seville", "Prague", "Nice", "Oslo", "Valencia"],
    "Valencia": ["Paris", "Lisbon", "Seville", "Lyon"],
    "Oslo": ["Tallinn", "Nice", "Paris", "Lyon"],
    "Lyon": ["Nice", "Prague", "Valencia", "Seville", "Oslo"],
    "Prague": ["Lyon", "Lisbon", "Tallinn", "Oslo", "Paris"],
    "Paris": ["Lisbon", "Oslo", "Nice", "Lyon", "Valencia", "Tallinn"],
    "Nice": ["Lyon", "Mykonos", "Oslo", "Paris"],
    "Seville": ["Lisbon", "Valencia", "Paris"],
    "Tallinn": ["Oslo", "Prague"],
    "Mykonos": ["Nice"]
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

# Meeting friends in Valencia between day 3 and day 4
for day in friends_meeting_days_valencia:
    solver.add(trip[day - 1] == cities.index("Valencia"))  # Adjust for 0-based index

# Meeting a friend in Oslo between day 13 and day 15
for day in friends_meeting_days_oslo:
    solver.add(trip[day - 1] == cities.index("Oslo"))  # Adjust for 0-based index

# Annual show in Seville between day 5 and day 9
for day in annual_show_days_seville:
    solver.add(trip[day - 1] == cities.index("Seville"))  # Adjust for 0-based index

# Wedding in Mykonos between day 21 and day 25
for day in wedding_days_mykonos:
    solver.add(trip[day - 1] == cities.index("Mykonos"))  # Adjust for 0-based index

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