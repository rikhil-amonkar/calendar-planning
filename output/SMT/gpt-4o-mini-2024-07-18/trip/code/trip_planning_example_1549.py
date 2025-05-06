from z3 import *

# Define the number of days and cities
total_days = 28
cities = [
    "Prague", "Tallinn", "Warsaw",
    "Porto", "Naples", "Milan", 
    "Lisbon", "Santorini", "Riga", 
    "Stockholm"
]

# Days assigned to each city with constraints
stay_duration = {
    "Prague": 5,
    "Tallinn": 3,
    "Warsaw": 2,
    "Porto": 3,
    "Naples": 5,
    "Milan": 3,
    "Lisbon": 5,
    "Santorini": 5,
    "Riga": 4,
    "Stockholm": 2
}

# Constraints for specific events
relatives_visit_days_tallinn = range(18, 21)  # Visit relatives in Tallinn (Day 18 to 20)
friends_meeting_days_milan = range(24, 27)     # Meet a friend in Milan (Day 24 to 26)
annual_show_days_riga = range(5, 9)            # Annual show in Riga (Day 5 to 8)

# Define direct flights between the cities
flights = {
    "Prague": ["Riga", "Milan", "Lisbon"],
    "Tallinn": ["Riga", "Prague"],
    "Warsaw": ["Naples", "Lisbon", "Riga", "Milan", "Porto", "Stockholm"],
    "Porto": ["Lisbon", "Milan", "Warsaw"],
    "Naples": ["Warsaw", "Milan", "Santorini"],
    "Milan": ["Naples", "Warsaw", "Porto", "Santorini", "Stockholm", "Riga"],
    "Lisbon": ["Warsaw", "Riga", "Porto", "Milan"],
    "Santorini": ["Milan", "Stockholm"],
    "Riga": ["Prague", "Tallinn", "Warsaw", "Lisbon", "Milan", "Stockholm"],
    "Stockholm": ["Milan", "Lisbon", "Santorini"]
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

# Visit relatives in Tallinn between days 18 and 20
for day in relatives_visit_days_tallinn:
    solver.add(trip[day - 1] == cities.index("Tallinn"))  # Adjust for 0-based index

# Meet friends in Milan between days 24 and 26
for day in friends_meeting_days_milan:
    solver.add(trip[day - 1] == cities.index("Milan"))  # Adjust for 0-based index

# Attend annual show in Riga between days 5 and 8
for day in annual_show_days_riga:
    solver.add(trip[day - 1] == cities.index("Riga"))  # Adjust for 0-based index

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