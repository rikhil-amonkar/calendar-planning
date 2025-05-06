from z3 import *

# Define the number of days and cities
total_days = 22
cities = [
    "Valencia", "Riga", "Prague", 
    "Mykonos", "Zurich", "Bucharest", "Nice"
]

# Days assigned to each city with constraints
stay_duration = {
    "Valencia": 5,
    "Riga": 5,
    "Prague": 3,
    "Mykonos": 3,
    "Zurich": 5,
    "Bucharest": 5,
    "Nice": 2
}

# Constraints for specific events
relatives_visit_days_prague = range(7, 10)   # Visiting relatives in Prague (Day 7 to Day 9)
wedding_days_mykonos = range(1, 4)            # Wedding in Mykonos (Day 1 to Day 3)

# Define direct flights between the cities
flights = {
    "Mykonos": ["Nice", "Zurich"],
    "Nice": ["Mykonos", "Riga", "Zurich"],
    "Prague": ["Bucharest", "Riga", "Zurich", "Valencia"],
    "Bucharest": ["Prague", "Riga", "Valencia", "Zurich"],
    "Riga": ["Nice", "Mykonos", "Prague", "Bucharest"],
    "Zurich": ["Mykonos", "Nice", "Prague", "Bucharest", "Riga", "Valencia"],
    "Valencia": ["Bucharest", "Prague"]
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

# Visiting relatives in Prague between day 7 and day 9
for day in relatives_visit_days_prague:
    solver.add(trip[day - 1] == cities.index("Prague"))  # Adjust for 0-based index

# Attend wedding in Mykonos between day 1 and day 3
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
    itinerary = []
    for day in range(total_days):
        city = cities[model[trip[day]].as_long()]
        itinerary.append(f"Day {day + 1}: {city}")
    print("\n".join(itinerary))
else:
    print("No valid trip plan found.")