from z3 import *

# Define the number of days and cities
total_days = 17
cities = [
    "Mykonos", "Riga", "Munich", 
    "Bucharest", "Rome", "Nice", "Krakow"
]

# Days assigned to each city with constraints
stay_duration = {
    "Mykonos": 3,
    "Riga": 3,
    "Munich": 4,
    "Bucharest": 4,
    "Rome": 4,
    "Nice": 3,
    "Krakow": 2
}

# Constraints for specific events
wedding_days_mykonos = range(4, 7)  # Wedding in Mykonos on days 4 to 6
conference_days_rome = [1, 4]         # Conference in Rome on days 1 and 4
annual_show_days_krakow = range(16, 18)  # Annual show in Krakow on days 16 and 17

# Define direct flights between the cities
flights = {
    "Mykonos": ["Munich", "Nice", "Rome"],
    "Riga": ["Nice", "Bucharest", "Munich", "Rome"],
    "Munich": ["Bucharest", "Krakow", "Mykonos", "Riga", "Rome", "Nice"],
    "Bucharest": ["Munich", "Riga", "Rome"],
    "Rome": ["Nice", "Munich", "Bucharest", "Mykonos", "Riga"],
    "Nice": ["Riga", "Munich", "Rome"],
    "Krakow": ["Munich"]
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

# Attend wedding in Mykonos between day 4 and day 6
for day in wedding_days_mykonos:
    solver.add(trip[day - 1] == cities.index("Mykonos"))  # Adjust for 0-based index

# Attend conference in Rome on days 1 and 4
for day in conference_days_rome:
    solver.add(trip[day - 1] == cities.index("Rome"))  # Adjust for 0-based index

# Attend annual show in Krakow on days 16 and 17
for day in annual_show_days_krakow:
    solver.add(trip[day - 1] == cities.index("Krakow"))  # Adjust for 0-based index

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