from z3 import *

# Define the number of days and cities
total_days = 15
cities = [
    "Dublin", "Helsinki", "Riga",
    "Reykjavik", "Vienna", "Tallinn"
]

# Days assigned to each city with constraints
stay_duration = {
    "Dublin": 5,
    "Helsinki": 3,
    "Riga": 3,
    "Reykjavik": 2,
    "Vienna": 2,
    "Tallinn": 5
}

# Constraints for specific events
friends_meeting_days_helsinki = range(3, 6)  # Meet friends in Helsinki (Day 3 to 5)
annual_show_days_vienna = [2]                  # Annual show in Vienna (Day 2 to 3)
wedding_days_tallinn = range(7, 11)            # Wedding in Tallinn (Day 7 to 10)

# Define direct flights between the cities
flights = {
    "Dublin": ["Helsinki", "Riga", "Vienna", "Tallinn", "Reykjavik"],
    "Helsinki": ["Riga", "Dublin", "Tallinn", "Vienna", "Reykjavik"],
    "Riga": ["Helsinki", "Dublin", "Tallinn", "Vienna"],
    "Reykjavik": ["Helsinki", "Dublin", "Vienna"],
    "Vienna": ["Helsinki", "Riga", "Dublin"],
    "Tallinn": ["Riga", "Dublin", "Helsinki"]
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

# Meet friends in Helsinki between day 3 and day 5
for day in friends_meeting_days_helsinki:
    solver.add(trip[day - 1] == cities.index("Helsinki"))  # Adjust for 0-based index

# Attend annual show in Vienna on day 2
solver.add(trip[1] == cities.index("Vienna"))  # Day 2 (adjust for 0-based index)

# Attend wedding in Tallinn between days 7 and 10
for day in wedding_days_tallinn:
    solver.add(trip[day - 1] == cities.index("Tallinn"))  # Adjust for 0-based index

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