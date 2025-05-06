from z3 import *

# Define the number of days and cities
total_days = 19
cities = [
    "Reykjavik", "Istanbul", "Edinburgh", 
    "Oslo", "Stuttgart", "Bucharest"
]

# Days assigned to each city with constraints
stay_duration = {
    "Reykjavik": 5,
    "Istanbul": 4,
    "Edinburgh": 5,
    "Oslo": 2,
    "Stuttgart": 3,
    "Bucharest": 5
}

# Constraints for specific events
friends_meeting_days_istanbul = range(5, 9)  # Meet friends in Istanbul (Day 5 to 8)
relatives_visit_days_oslo = [8, 9]             # Visit relatives in Oslo (Day 8 and 9)

# Define direct flights between the cities
flights = {
    "Bucharest": ["Oslo", "Istanbul"],
    "Istanbul": ["Oslo", "Bucharest", "Edinburgh", "Stuttgart"],
    "Reykjavik": ["Stuttgart"],
    "Oslo": ["Reykjavik", "Bucharest", "Istanbul", "Edinburgh"],
    "Stuttgart": ["Reykjavik", "Edinburgh", "Istanbul"],
    "Edinburgh": ["Stuttgart", "Istanbul", "Oslo"]
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

# Meet friends in Istanbul between day 5 and day 8
for day in friends_meeting_days_istanbul:
    solver.add(trip[day - 1] == cities.index("Istanbul"))  # Adjust for 0-based index

# Visit relatives in Oslo between day 8 and day 9
for day in relatives_visit_days_oslo:
    solver.add(trip[day - 1] == cities.index("Oslo"))  # Adjust for 0-based index

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