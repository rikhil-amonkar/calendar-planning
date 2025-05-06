from z3 import *

# Define the number of days and cities
total_days = 22
cities = [
    "Berlin", "Split", "Bucharest", 
    "Riga", "Lisbon", "Tallinn", "Lyon"
]

# Days assigned to each city with constraints
stay_duration = {
    "Berlin": 5,
    "Split": 3,
    "Bucharest": 3,
    "Riga": 5,
    "Lisbon": 3,
    "Tallinn": 4,
    "Lyon": 5
}

# Constraints for specific events
annual_show_days_berlin = range(1, 6)    # Annual show in Berlin (Day 1 to Day 5)
relatives_visit_days_bucharest = range(13, 16)  # Visit relatives in Bucharest (Day 13 to Day 15)
wedding_days_lyon = range(7, 12)          # Wedding in Lyon (Day 7 to Day 11)

# Define direct flights between the cities
flights = {
    "Berlin": ["Lisbon", "Riga", "Split", "Tallinn"],
    "Split": ["Lyon"],
    "Bucharest": ["Lisbon", "Riga", "Lyon"],
    "Riga": ["Bucharest", "Lisbon", "Tallinn", "Berlin"],
    "Lisbon": ["Bucharest", "Riga", "Berlin"],
    "Tallinn": ["Riga", "Berlin"],
    "Lyon": ["Split", "Lisbon", "Bucharest"]
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for each day
trip = [Int(f'day_{i}') for i in range(total_days)]

# Each day must refer to one of the cities
for day in trip:
    solver.add(Or([day == cities.index(city) for city in cities]))

# Count the days spent in each city
city_count = {city: Sum([If(trip[day] == cities.index(city), 1, 0) for day in range(total_days)]) for city in cities}

# Enforce stay durations
for city, duration in stay_duration.items():
    solver.add(city_count[city] == duration)

# Annual show in Berlin between day 1 and day 5
for day in annual_show_days_berlin:
    solver.add(trip[day - 1] == cities.index("Berlin"))  # Adjust for 0-based index

# Visiting relatives in Bucharest between day 13 and day 15
for day in relatives_visit_days_bucharest:
    solver.add(trip[day - 1] == cities.index("Bucharest"))  # Adjust for 0-based index

# Wedding in Lyon between day 7 and day 11
for day in wedding_days_lyon:
    solver.add(trip[day - 1] == cities.index("Lyon"))  # Adjust for 0-based index

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