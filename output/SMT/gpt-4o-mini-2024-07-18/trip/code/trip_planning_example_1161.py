from z3 import *

# Define the number of days and cities
total_days = 18
cities = [
    "Mykonos", "Krakow", "Vilnius",
    "Helsinki", "Dubrovnik", "Oslo", 
    "Madrid", "Paris"
]

# Days assigned to each city with constraints
stay_duration = {
    "Mykonos": 4,
    "Krakow": 5,
    "Vilnius": 2,
    "Helsinki": 2,
    "Dubrovnik": 3,
    "Oslo": 2,
    "Madrid": 5,
    "Paris": 2
}

# Constraints for specific events
relatives_visit_mykonos = range(15, 19)   # Relatives in Mykonos (Day 15 to Day 18)
annual_show_dubrovnik = range(2, 5)        # Annual show in Dubrovnik (Day 2 to Day 4)
friends_meeting_oslo = range(1, 3)          # Meet friends in Oslo (Day 1 to Day 2)

# Define direct flights between the cities
flights = {
    "Mykonos": ["Madrid"],
    "Krakow": ["Oslo", "Vilnius", "Paris"],
    "Vilnius": ["Helsinki", "Krakow", "Oslo", "Paris"],
    "Helsinki": ["Oslo", "Vilnius", "Krakow", "Dubrovnik", "Madrid", "Paris"],
    "Dubrovnik": ["Helsinki", "Madrid"],
    "Oslo": ["Krakow", "Madrid", "Helsinki", "Paris", "Dubrovnik"],
    "Madrid": ["Mykonos", "Dubrovnik", "Paris", "Oslo"],
    "Paris": ["Madrid", "Krakow", "Vilnius", "Helsinki", "Oslo"]
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

# Relatives in Mykonos between day 15 and day 18
for day in relatives_visit_mykonos:
    solver.add(trip[day - 1] == cities.index("Mykonos"))  # Adjust for 0-based index

# Attend annual show in Dubrovnik between day 2 and day 4
for day in annual_show_dubrovnik:
    solver.add(trip[day - 1] == cities.index("Dubrovnik"))  # Adjust for 0-based index

# Meet friends in Oslo between day 1 and day 2
for day in friends_meeting_oslo:
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