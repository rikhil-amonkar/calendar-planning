from z3 import *

# Define the number of days and cities
total_days = 18
cities = [
    "Porto", "Geneva", "Mykonos", 
    "Manchester", "Hamburg", "Naples", "Frankfurt"
]

# Days assigned to each city with constraints
stay_duration = {
    "Porto": 2,
    "Geneva": 3,
    "Mykonos": 3,
    "Manchester": 4,
    "Hamburg": 5,
    "Naples": 5,
    "Frankfurt": 2
}

# Constraints for specific events
meeting_days_mykonos = range(10, 13)      # Meeting a friend in Mykonos (Day 10 to Day 12)
wedding_days_manchester = range(15, 19)    # Wedding in Manchester (Day 15 to Day 18)
annual_show_days_frankfurt = [5, 6]        # Annual show in Frankfurt (Day 5 and Day 6)

# Define direct flights between the cities
flights = {
    "Porto": ["Hamburg", "Frankfurt", "Geneva", "Manchester"],
    "Geneva": ["Hamburg", "Frankfurt", "Mykonos", "Naples", "Manchester", "Porto"],
    "Mykonos": ["Geneva", "Naples"],
    "Manchester": ["Naples", "Hamburg", "Frankfurt", "Geneva", "Porto"],
    "Hamburg": ["Frankfurt", "Geneva", "Porto", "Manchester"],
    "Naples": ["Mykonos", "Frankfurt", "Geneva", "Manchester"],
    "Frankfurt": ["Hamburg", "Geneva", "Porto", "Naples", "Manchester"],
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

# Meeting a friend in Mykonos between day 10 and day 12
for day in meeting_days_mykonos:
    solver.add(trip[day - 1] == cities.index("Mykonos"))  # Adjust for 0-based index

# Wedding in Manchester between day 15 and day 18
for day in wedding_days_manchester:
    solver.add(trip[day - 1] == cities.index("Manchester"))  # Adjust for 0-based index

# Annual show in Frankfurt between day 5 and day 6
for day in annual_show_days_frankfurt:
    solver.add(trip[day - 1] == cities.index("Frankfurt"))  # Adjust for 0-based index

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