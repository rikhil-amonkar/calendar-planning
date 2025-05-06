from z3 import *

# Define the number of days and cities
total_days = 22
cities = [
    "Brussels", "Helsinki", "Split", 
    "Dubrovnik", "Istanbul", "Milan", 
    "Vilnius", "Frankfurt"
]

# Days assigned to each city with constraints
stay_duration = {
    "Brussels": 3,
    "Helsinki": 3,
    "Split": 4,
    "Dubrovnik": 2,
    "Istanbul": 5,
    "Milan": 4,
    "Vilnius": 5,
    "Frankfurt": 3
}

# Constraints for specific events
annual_show_istanbul = range(1, 6)      # Annual show in Istanbul (Day 1 to Day 5)
wedding_days_frankfurt = range(16, 18)  # Wedding in Frankfurt (Day 16 to Day 18)
workshop_days_vilnius = range(18, 23)    # Workshop in Vilnius (Day 18 to Day 22)

# Define direct flights between the cities
flights = {
    "Brussels": ["Vilnius", "Helsinki", "Istanbul", "Milan"],
    "Helsinki": ["Vilnius", "Dubrovnik", "Istanbul", "Frankfurt"],
    "Split": ["Frankfurt", "Vilnius", "Milan", "Helsinki"],
    "Dubrovnik": ["Istanbul", "Helsinki", "Frankfurt"],
    "Istanbul": ["Brussels", "Helsinki", "Milan", "Frankfurt"],
    "Milan": ["Frankfurt", "Split", "Vilnius", "Helsinki"],
    "Vilnius": ["Brussels", "Helsinki", "Milan", "Split", "Frankfurt"],
    "Frankfurt": ["Milan", "Dubrovnik", "Split", "Vilnius", "Helsinki"]
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

# Attend annual show in Istanbul between day 1 and day 5
for day in annual_show_istanbul:
    solver.add(trip[day - 1] == cities.index("Istanbul"))  # Adjust for 0-based index

# Attend wedding in Frankfurt between day 16 and day 18
for day in wedding_days_frankfurt:
    solver.add(trip[day - 1] == cities.index("Frankfurt"))  # Adjust for 0-based index

# Attend workshop in Vilnius between day 18 and day 22
for day in workshop_days_vilnius:
    solver.add(trip[day - 1] == cities.index("Vilnius"))  # Adjust for 0-based index

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