from z3 import *

# Define the number of days and cities
total_days = 23
cities = [
    "Riga", "Manchester", "Bucharest", 
    "Florence", "Vienna", "Istanbul", 
    "Reykjavik", "Stuttgart"
]

# Days assigned to each city with constraints
stay_duration = {
    "Riga": 4,
    "Manchester": 5,
    "Bucharest": 4,
    "Florence": 4,
    "Vienna": 2,
    "Istanbul": 2,
    "Reykjavik": 4,
    "Stuttgart": 5
}

# Constraints for specific events
workshop_days_bucharest = range(16, 20)  # Workshop in Bucharest (Day 16 to Day 19)
annual_show_days_istanbul = [12, 13]      # Annual show in Istanbul (Day 12 and Day 13)

# Define direct flights between the cities
flights = {
    "Bucharest": ["Vienna", "Riga", "Istanbul", "Manchester"],
    "Vienna": ["Florence", "Reykjavik", "Stuttgart", "Istanbul", "Bucharest", "Manchester", "Riga"],
    "Reykjavik": ["Vienna", "Stuttgart"],
    "Manchester": ["Vienna", "Riga", "Istanbul", "Bucharest", "Stuttgart"],
    "Riga": ["Vienna", "Bucharest", "Manchester", "Istanbul"],
    "Istanbul": ["Vienna", "Riga", "Bucharest", "Stuttgart", "Manchester"],
    "Florence": ["Vienna"],
    "Stuttgart": ["Vienna", "Reykjavik", "Istanbul", "Manchester"]
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

# Workshop in Bucharest between day 16 and day 19
for day in workshop_days_bucharest:
    solver.add(trip[day - 1] == cities.index("Bucharest"))  # Adjust for 0-based index

# Annual show in Istanbul on day 12 and 13
for day in annual_show_days_istanbul:
    solver.add(trip[day - 1] == cities.index("Istanbul"))  # Adjust for 0-based index

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