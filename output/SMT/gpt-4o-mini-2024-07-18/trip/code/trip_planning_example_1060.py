from z3 import *

# Define the number of days and cities
total_days = 25
cities = [
    "Stuttgart", "Istanbul", "Vilnius", 
    "Seville", "Geneva", "Valencia", 
    "Munich", "Reykjavik"
]

# Days assigned to each city with constraints
stay_duration = {
    "Stuttgart": 4,
    "Istanbul": 4,
    "Vilnius": 4,
    "Seville": 3,
    "Geneva": 5,
    "Valencia": 5,
    "Munich": 3,
    "Reykjavik": 4
}

# Constraints for specific events
conference_days_stuttgart = [4, 7]                # Conference in Stuttgart (Day 4 and Day 7)
relatives_visit_days_istanbul = range(19, 23)     # Visiting relatives in Istanbul (Day 19 to Day 22)
annual_show_days_munich = range(13, 16)           # Annual show in Munich (Day 13 to Day 15)
workshop_days_reykjavik = range(1, 5)              # Workshop in Reykjavik (Day 1 to Day 4)

# Define direct flights between the cities
flights = {
    "Stuttgart": ["Valencia", "Istanbul"],
    "Istanbul": ["Geneva", "Vilnius", "Stuttgart", "Valencia"],
    "Vilnius": ["Munich", "Istanbul"],
    "Seville": ["Valencia", "Munich"],
    "Geneva": ["Munich", "Istanbul", "Valencia"],
    "Valencia": ["Stuttgart", "Seville", "Istanbul", "Geneva", "Munich"],
    "Munich": ["Reykjavik", "Geneva", "Vilnius", "Istanbul", "Seville"],
    "Reykjavik": ["Munich", "Stuttgart"]
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

# Attend conferences in Stuttgart on day 4 and day 7
for day in conference_days_stuttgart:
    solver.add(trip[day - 1] == cities.index("Stuttgart"))  # Adjust for 0-based index

# Visiting relatives in Istanbul between day 19 and day 22
for day in relatives_visit_days_istanbul:
    solver.add(trip[day - 1] == cities.index("Istanbul"))  # Adjust for 0-based index

# Attend annual show in Munich between day 13 and day 15
for day in annual_show_days_munich:
    solver.add(trip[day - 1] == cities.index("Munich"))  # Adjust for 0-based index

# Attend workshop in Reykjavik between day 1 and day 4
for day in workshop_days_reykjavik:
    solver.add(trip[day - 1] == cities.index("Reykjavik"))  # Adjust for 0-based index

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