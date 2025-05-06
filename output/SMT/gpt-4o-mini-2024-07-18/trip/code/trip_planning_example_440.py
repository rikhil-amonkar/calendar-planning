from z3 import *

# Define the number of days and cities
total_days = 12
cities = [
    "Split", "Helsinki", "Reykjavik", 
    "Vilnius", "Geneva"
]

# Days assigned to each city with constraints
stay_duration = {
    "Split": 2,
    "Helsinki": 2,
    "Reykjavik": 3,
    "Vilnius": 3,
    "Geneva": 6
}

# Constraints for specific events
wedding_days_reykjavik = range(10, 13)  # Wedding in Reykjavik (Day 10 to 12)
relatives_visit_days_vilnius = range(7, 10)  # Visit relatives in Vilnius (Day 7 to 9)

# Define direct flights between the cities
flights = {
    "Split": ["Helsinki", "Geneva", "Vilnius"],
    "Helsinki": ["Reykjavik", "Split", "Vilnius"],
    "Reykjavik": ["Helsinki"],
    "Vilnius": ["Helsinki", "Split"],
    "Geneva": ["Split", "Helsinki"]
}

# Initialize the Z3 solver
solver = Solver()

# Create variables for each day of the trip
trip = [Int(f'day_{i + 1}') for i in range(total_days)]

# Each day must refer to one of the cities
for day in trip:
    solver.add(Or([day == cities.index(city) for city in cities]))

# Count the days spent in each city
city_count = {city: Sum([If(trip[day] == cities.index(city), 1, 0) for day in range(total_days)]) for city in cities}

# Enforce stay durations
for city, duration in stay_duration.items():
    solver.add(city_count[city] == duration)

# Attend wedding in Reykjavik between days 10 and 12
for day in wedding_days_reykjavik:
    solver.add(trip[day - 1] == cities.index("Reykjavik"))  # Adjust for 0-based index

# Visit relatives in Vilnius between days 7 and 9
for day in relatives_visit_days_vilnius:
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