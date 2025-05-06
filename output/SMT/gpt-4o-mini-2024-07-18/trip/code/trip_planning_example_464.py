from z3 import *

# Define the number of days and cities
total_days = 18
cities = ["Krakow", "Frankfurt", "Oslo", "Dubrovnik", "Naples"]

# Days assigned to each city with constraints
stay_duration = {
    "Krakow": 5,
    "Frankfurt": 4,
    "Oslo": 3,
    "Dubrovnik": 5,
    "Naples": 5
}

# Constraints for specific events
relatives_visit_days_oslo = range(16, 19)  # Visit relatives in Oslo (Day 16 to Day 18)
friends_meeting_days_dubrovnik = range(5, 10)  # Friends meeting in Dubrovnik (Day 5 to Day 9)

# Define direct flights between the cities
flights = {
    "Krakow": ["Frankfurt", "Oslo"],
    "Frankfurt": ["Krakow", "Oslo", "Dubrovnik", "Naples"],
    "Oslo": ["Krakow", "Frankfurt", "Dubrovnik", "Naples"],
    "Dubrovnik": ["Oslo", "Frankfurt", "Naples"],
    "Naples": ["Oslo", "Dubrovnik", "Frankfurt"]
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

# Visiting relatives in Oslo between day 16 and day 18
for day in relatives_visit_days_oslo:
    solver.add(trip[day - 1] == cities.index("Oslo"))  # Adjust for 0-based index

# Meeting friends in Dubrovnik between day 5 and day 9
for day in friends_meeting_days_dubrovnik:
    solver.add(trip[day - 1] == cities.index("Dubrovnik"))  # Adjust for 0-based index

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