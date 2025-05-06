from z3 import *

# Define the number of days and cities
total_days = 27
cities = [
    "Istanbul", "Vienna", "Riga",
    "Brussels", "Madrid", "Vilnius",
    "Venice", "Geneva", "Munich", "Reykjavik"
]

# Days assigned to each city with constraints
stay_duration = {
    "Istanbul": 4,
    "Vienna": 4,
    "Riga": 2,
    "Brussels": 2,
    "Madrid": 4,
    "Vilnius": 4,
    "Venice": 5,
    "Geneva": 4,
    "Munich": 5,
    "Reykjavik": 2
}

# Constraints for specific events
wedding_days_brussels = [26, 27]                     # Wedding in Brussels (Day 26 to Day 27)
meeting_days_vilnius = range(20, 24)                  # Meeting friends in Vilnius (Day 20 to Day 23)
workshop_days_venice = range(7, 12)                   # Workshop in Venice (Day 7 to Day 11)
relatives_visit_days_geneva = range(1, 5)             # Visiting relatives in Geneva (Day 1 to Day 4)

# Define direct flights between the cities
flights = {
    "Munich": ["Vienna", "Madrid", "Reykjavik", "Brussels", "Venice"],
    "Istanbul": ["Brussels", "Vienna", "Riga", "Vilnius"],
    "Vienna": ["Vilnius", "Istanbul", "Madrid", "Riga", "Munich", "Brussels"],
    "Riga": ["Brussels", "Istanbul", "Munich", "Vilnius"],
    "Brussels": ["Istanbul", "Venice", "Riga", "Vienna", "Geneva", "Madrid"],
    "Madrid": ["Vienna", "Munich", "Venice", "Brussels"],
    "Vilnius": ["Vienna", "Istanbul", "Riga"],
    "Venice": ["Brussels", "Munich", "Madrid", "Vienna", "Istanbul"],
    "Geneva": ["Istanbul", "Vienna", "Brussels", "Munich"],
    "Reykjavik": ["Munich", "Vienna", "Brussels"]
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

# Wedding in Brussels on day 26 and 27
for day in wedding_days_brussels:
    solver.add(trip[day - 1] == cities.index("Brussels"))  # Adjust for 0-based index

# Meeting friends in Vilnius between day 20 and day 23
for day in meeting_days_vilnius:
    solver.add(trip[day - 1] == cities.index("Vilnius"))  # Adjust for 0-based index

# Workshop in Venice between day 7 and day 11
for day in workshop_days_venice:
    solver.add(trip[day - 1] == cities.index("Venice"))  # Adjust for 0-based index

# Visiting relatives in Geneva between day 1 and day 4
for day in relatives_visit_days_geneva:
    solver.add(trip[day - 1] == cities.index("Geneva"))  # Adjust for 0-based index

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