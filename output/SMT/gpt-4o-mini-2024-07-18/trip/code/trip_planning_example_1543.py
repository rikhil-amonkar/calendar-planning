from z3 import *

# Define the number of days and cities
total_days = 26
cities = [
    "Prague", "Warsaw", "Dublin", 
    "Athens", "Vilnius", "Porto",
    "London", "Seville", "Lisbon", "Dubrovnik"
]

# Days assigned to each city with constraints
stay_duration = {
    "Prague": 3,
    "Warsaw": 4,
    "Dublin": 3,
    "Athens": 3,
    "Vilnius": 4,
    "Porto": 5,
    "London": 3,
    "Seville": 2,
    "Lisbon": 5,
    "Dubrovnik": 3
}

# Constraints for specific events
workshop_days_prague = range(1, 4)  # Workshop in Prague (Day 1 to Day 3)
conference_days_porto = [16, 20]     # Conference in Porto (Day 16 and Day 20)
friends_meeting_days_warsaw = range(20, 24)  # Meeting friends in Warsaw (Day 20 to Day 23)
wedding_days_london = range(3, 6)    # Wedding in London (Day 3 to Day 5)
relatives_visit_days_lisbon = range(5, 10)  # Visit relatives in Lisbon (Day 5 to Day 9)

# Define direct flights between the cities
flights = {
    "Warsaw": ["Vilnius", "Lisbon", "Porto", "Dublin", "Athens"],
    "Prague": ["Athens", "Lisbon", "London", "Warsaw", "Dublin"],
    "Dublin": ["London", "Seville", "Porto", "Athens", "Lisbon"],
    "Athens": ["Vilnius", "Dublin", "Warsaw", "Prague", "Dubrovnik"],
    "Vilnius": ["Warsaw", "Athens"],
    "Porto": ["Warsaw", "Lisbon", "Seville"],
    "London": ["Warsaw", "Lisbon", "Dublin", "Athens", "Prague"],
    "Seville": ["Dublin", "Porto"],
    "Lisbon": ["Porto", "Athens", "Dublin", "Warsaw"],
    "Dubrovnik": ["Athens", "Dublin"]
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

# Attend workshop in Prague between day 1 and day 3
for day in workshop_days_prague:
    solver.add(trip[day - 1] == cities.index("Prague"))  # Adjust for 0-based index

# Attend conference in Porto on day 16 and day 20
for day in conference_days_porto:
    solver.add(trip[day - 1] == cities.index("Porto"))  # Adjust for 0-based index

# Meet friends in Warsaw between day 20 and day 23
for day in friends_meeting_days_warsaw:
    solver.add(trip[day - 1] == cities.index("Warsaw"))  # Adjust for 0-based index

# Attend wedding in London between day 3 and day 5
for day in wedding_days_london:
    solver.add(trip[day - 1] == cities.index("London"))  # Adjust for 0-based index

# Visit relatives in Lisbon between day 5 and day 9
for day in relatives_visit_days_lisbon:
    solver.add(trip[day - 1] == cities.index("Lisbon"))  # Adjust for 0-based index

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