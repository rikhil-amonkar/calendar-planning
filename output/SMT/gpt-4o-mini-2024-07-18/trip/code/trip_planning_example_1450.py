from z3 import *

# Define the number of days and cities
total_days = 32
cities = [
    "Stockholm", "Hamburg", "Florence", 
    "Istanbul", "Oslo", "Vilnius", 
    "Santorini", "Munich", "Frankfurt", "Krakow"
]

# Days assigned to each city with constraints
stay_duration = {
    "Stockholm": 3,
    "Hamburg": 5,
    "Florence": 2,
    "Istanbul": 5,
    "Oslo": 5,
    "Vilnius": 5,
    "Santorini": 2,
    "Munich": 5,
    "Frankfurt": 4,
    "Krakow": 5
}

# Constraints for specific events
annual_show_days_ Istanbul = range(25, 30)  # Annual show in Istanbul (Day 25 to Day 29)
workshop_days_krakow = range(5, 9)           # Workshop in Krakow (Day 5 to Day 9)

# Define direct flights between the cities
flights = {
    "Oslo": ["Stockholm", "Istanbul", "Krakow", "Vilnius", "Hamburg", "Frankfurt"],
    "Stockholm": ["Oslo", "Hamburg", "Munich", "Santorini", "Istanbul", "Krakow"],
    "Hamburg": ["Stockholm", "Munich", "Istanbul", "Oslo"],
    "Florence": ["Munich", "Frankfurt"],
    "Istanbul": ["Oslo", "Krakow", "Frankfurt", "Stockholm"],
    "Vilnius": ["Krakow", "Oslo", "Frankfurt", "Istanbul"],
    "Santorini": ["Stockholm", "Oslo"],
    "Munich": ["Hamburg", "Florence", "Krakow", "Istanbul", "Frankfurt", "Stockholm"],
    "Frankfurt": ["Krakow", "Florence", "Istanbul", "Oslo", "Hamburg", "Munich"],
    "Krakow": ["Istanbul", "Frankfurt", "Vilnius", "Munich", "Oslo", "Stockholm"]
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

# Attend annual show in Istanbul between day 25 and day 29
for day in annual_show_days_ Istanbul:
    solver.add(trip[day - 1] == cities.index("Istanbul"))  # Adjust for 0-based index

# Attend workshop in Krakow between day 5 and day 9
for day in workshop_days_krakow:
    solver.add(trip[day - 1] == cities.index("Krakow"))  # Adjust for 0-based index

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