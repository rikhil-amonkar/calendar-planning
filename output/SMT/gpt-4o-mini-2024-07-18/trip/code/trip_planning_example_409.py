from z3 import *

# Define the number of days and cities
total_days = 12
cities = [
    "Hamburg", "Zurich", "Helsinki", 
    "Bucharest", "Split"
]

# Days assigned to each city with constraints
stay_duration = {
    "Hamburg": 2,
    "Zurich": 3,
    "Helsinki": 2,
    "Bucharest": 2,
    "Split": 7
}

# Constraints for specific events
wedding_days_zurich = range(1, 4)  # Wedding in Zurich between day 1 and day 3
conference_days_split = [4, 10]      # Attend conference in Split on days 4 and 10

# Define direct flights between the cities
flights = {
    "Hamburg": ["Bucharest", "Zurich", "Helsinki", "Split"],
    "Zurich": ["Helsinki", "Hamburg", "Bucharest", "Split"],
    "Helsinki": ["Hamburg", "Zurich", "Split"],
    "Bucharest": ["Hamburg", "Zurich"],
    "Split": ["Hamburg", "Zurich", "Helsinki"]
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

# Attend wedding in Zurich between day 1 and day 3
for day in wedding_days_zurich:
    solver.add(trip[day - 1] == cities.index("Zurich"))  # Adjust for 0-based index

# Attend conference in Split on days 4 and 10
for day in conference_days_split:
    solver.add(trip[day - 1] == cities.index("Split"))  # Adjust for 0-based index

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