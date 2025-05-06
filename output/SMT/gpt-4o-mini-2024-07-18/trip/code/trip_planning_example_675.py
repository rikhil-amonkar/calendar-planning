from z3 import *

# Define the number of days and cities
total_days = 16
cities = [
    "Dubrovnik", "Split", "Milan", 
    "Porto", "Krakow", "Munich"
]

# Days assigned to each city with constraints
stay_duration = {
    "Dubrovnik": 4,
    "Split": 3,
    "Milan": 3,
    "Porto": 4,
    "Krakow": 2,
    "Munich": 5
}

# Constraints for specific events
wedding_days_milan = range(11, 14)  # Wedding in Milan between day 11 and day 13
friends_meeting_days_krakow = range(8, 10)  # Meeting friends in Krakow (Day 8 to Day 9)
annual_show_days_munich = range(4, 9)  # Annual show in Munich (Day 4 to Day 8)

# Define direct flights between the cities
flights = {
    "Munich": ["Porto", "Krakow", "Milan", "Dubrovnik", "Split"],
    "Dubrovnik": ["Munich"],
    "Split": ["Milan", "Krakow", "Munich"],
    "Milan": ["Porto", "Split", "Krakow", "Munich"],
    "Porto": ["Milan", "Munich"],
    "Krakow": ["Munich", "Split", "Milan"]
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

# Attend wedding in Milan between day 11 and day 13
for day in wedding_days_milan:
    solver.add(trip[day - 1] == cities.index("Milan"))  # Adjust for 0-based index

# Meet friends in Krakow between day 8 and day 9
for day in friends_meeting_days_krakow:
    solver.add(trip[day - 1] == cities.index("Krakow"))  # Adjust for 0-based index

# Attend annual show in Munich between day 4 and day 8
for day in annual_show_days_munich:
    solver.add(trip[day - 1] == cities.index("Munich"))  # Adjust for 0-based index

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