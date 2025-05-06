from z3 import *

# Define the number of days and cities
total_days = 26
cities = [
    "Bucharest", "Venice", "Prague", 
    "Frankfurt", "Zurich", "Florence", "Tallinn"
]

# Days assigned to each city with constraints
stay_duration = {
    "Bucharest": 3,
    "Venice": 5,
    "Prague": 4,
    "Frankfurt": 5,
    "Zurich": 5,
    "Florence": 5,
    "Tallinn": 5
}

# Constraints for specific events
wedding_days_venice = range(22, 27)          # Wedding in Venice (Day 22 to Day 26)
annual_show_days_frankfurt = range(12, 17)   # Annual show in Frankfurt (Day 12 to Day 16)
friends_meeting_days_tallinn = range(8, 13)   # Meeting friends in Tallinn (Day 8 to Day 12)

# Define direct flights between the cities
flights = {
    "Bucharest": ["Frankfurt", "Prague", "Zurich"],
    "Venice": ["Frankfurt", "Zurich"],
    "Prague": ["Tallinn", "Zurich", "Florence", "Frankfurt", "Bucharest"],
    "Frankfurt": ["Bucharest", "Venice", "Zurich", "Tallinn", "Prague"],
    "Zurich": ["Bucharest", "Florence", "Frankfurt", "Venice", "Prague", "Tallinn"],
    "Florence": ["Zurich", "Prague", "Frankfurt"],
    "Tallinn": ["Prague", "Frankfurt", "Zurich"]
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

# Attend wedding in Venice between day 22 and day 26
for day in wedding_days_venice:
    solver.add(trip[day - 1] == cities.index("Venice"))  # Adjust for 0-based index

# Attend annual show in Frankfurt between day 12 and day 16
for day in annual_show_days_frankfurt:
    solver.add(trip[day - 1] == cities.index("Frankfurt"))  # Adjust for 0-based index

# Meet friends in Tallinn between day 8 and day 12
for day in friends_meeting_days_tallinn:
    solver.add(trip[day - 1] == cities.index("Tallinn"))  # Adjust for 0-based index

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