from z3 import *

# Define the number of days and cities
total_days = 12
cities = [
    "Frankfurt", "Naples", "Helsinki", 
    "Lyon", "Prague"
]

# Days assigned to each city with constraints
stay_duration = {
    "Frankfurt": 3,
    "Naples": 4,
    "Helsinki": 4,
    "Lyon": 3,
    "Prague": 2
}

# Constraints for specific events
annual_show_days_helsinki = range(2, 6)        # Annual show in Helsinki (Day 2 to Day 5)
workshop_days_prague = [1, 2]                   # Workshop in Prague (Day 1 to Day 2)

# Define direct flights between the cities
flights = {
    "Prague": ["Lyon", "Frankfurt", "Helsinki"],
    "Frankfurt": ["Lyon", "Naples", "Helsinki", "Prague"],
    "Naples": ["Frankfurt", "Helsinki"],
    "Helsinki": ["Naples", "Frankfurt", "Prague"],
    "Lyon": ["Prague", "Frankfurt"]
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

# Annual show in Helsinki between day 2 and day 5
for day in annual_show_days_helsinki:
    solver.add(trip[day - 1] == cities.index("Helsinki"))  # Adjust for 0-based index

# Workshop in Prague on day 1 and day 2
for day in workshop_days_prague:
    solver.add(trip[day - 1] == cities.index("Prague"))  # Adjust for 0-based index

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