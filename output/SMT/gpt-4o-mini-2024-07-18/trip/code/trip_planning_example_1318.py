from z3 import *

# Define the number of days and cities
total_days = 25
cities = [
    "Oslo", "Helsinki", "Edinburgh", 
    "Riga", "Tallinn", "Budapest", 
    "Vilnius", "Porto", "Geneva"
]

# Days assigned to each city with constraints
stay_duration = {
    "Oslo": 2,
    "Helsinki": 2,
    "Edinburgh": 3,
    "Riga": 2,
    "Tallinn": 5,
    "Budapest": 5,
    "Vilnius": 5,
    "Porto": 5,
    "Geneva": 4
}

# Constraints for specific events
friends_meeting_oslo = range(24, 26)  # Meet a friend in Oslo (Day 24 to 25)
wedding_days_tallinn = range(4, 9)      # Wedding in Tallinn (Day 4 to 8)

# Define direct flights between the cities
flights = {
    "Oslo": ["Porto", "Riga", "Geneva", "Tallinn", "Helsinki", "Budapest", "Edinburgh", "Vilnius"],
    "Helsinki": ["Vilnius", "Budapest", "Oslo", "Edinburgh", "Riga", "Tallinn"],
    "Edinburgh": ["Budapest", "Geneva", "Porto", "Oslo", "Helsinki", "Riga"],
    "Riga": ["Tallinn", "Oslo", "Helsinki", "Vilnius", "Edinburgh"],
    "Tallinn": ["Riga", "Vilnius", "Oslo", "Helsinki"],
    "Budapest": ["Edinburgh", "Helsinki", "Geneva", "Oslo"],
    "Vilnius": ["Helsinki", "Riga", "Tallinn", "Oslo"],
    "Porto": ["Oslo", "Edinburgh"],
    "Geneva": ["Edinburgh", "Budapest", "Oslo", "Helsinki"]
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

# Meet friend in Oslo on days 24 and 25
for day in friends_meeting_oslo:
    solver.add(trip[day - 1] == cities.index("Oslo"))  # Adjust for 0-based index

# Attend wedding in Tallinn between day 4 and day 8
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