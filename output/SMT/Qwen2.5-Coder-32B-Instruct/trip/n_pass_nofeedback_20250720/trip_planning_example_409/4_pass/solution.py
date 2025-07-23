from z3 import *
import json

# Define the cities and their respective stay durations
cities = ['Hamburg', 'Zurich', 'Helsinki', 'Bucharest', 'Split']
stay_durations = {'Hamburg': 2, 'Zurich': 3, 'Helsinki': 2, 'Bucharest': 2, 'Split': 7}

# Define the direct flight connections
flights = {
    ('Zurich', 'Helsinki'), ('Hamburg', 'Bucharest'), ('Helsinki', 'Hamburg'),
    ('Zurich', 'Hamburg'), ('Zurich', 'Bucharest'), ('Zurich', 'Split'),
    ('Helsinki', 'Split'), ('Split', 'Hamburg')
}

# Create a solver instance
solver = Solver()

# Define the start day for each city as a Z3 integer variable
start_days = {city: Int(f'start_{city}') for city in cities}

# Add constraints for the stay durations
for city, duration in stay_durations.items():
    solver.add(start_days[city] >= 1)
    solver.add(start_days[city] + duration <= 12)

# Add constraints for the specific requirements
# Stay in Zurich between day 1 and day 3
solver.add(start_days['Zurich'] <= 1)
solver.add(start_days['Zurich'] + stay_durations['Zurich'] >= 3)

# Attend conference in Split on day 4 and day 10
solver.add(Or(
    And(start_days['Split'] <= 4, start_days['Split'] + stay_durations['Split'] >= 5),
    And(start_days['Split'] <= 10, start_days['Split'] + stay_durations['Split'] >= 11)
))

# Add constraints for direct flights
for i in range(len(cities)):
    for j in range(i + 1, len(cities)):
        city1, city2 = cities[i], cities[j]
        if (city1, city2) not in flights and (city2, city1) not in flights:
            # If there is no direct flight between city1 and city2, ensure they do not overlap
            solver.add(Or(
                start_days[city1] + stay_durations[city1] <= start_days[city2],
                start_days[city2] + stay_durations[city2] <= start_days[city1]
            ))

# Ensure that transitions between cities are valid
for i in range(len(cities)):
    for j in range(i + 1, len(cities)):
        city1, city2 = cities[i], cities[j]
        if (city1, city2) in flights or (city2, city1) in flights:
            # If there is a direct flight between city1 and city2, ensure they can transition
            solver.add(Or(
                start_days[city1] + stay_durations[city1] == start_days[city2],
                start_days[city2] + stay_durations[city2] == start_days[city1]
            ))

# Ensure that the total number of days is exactly 12
total_days = 12
day_in_city = [Bool(f'day_{d}_in_{city}') for d in range(1, total_days + 1) for city in cities]

# Add constraints for each day
for d in range(1, total_days + 1):
    # Exactly one city per day
    solver.add(Exactly(1, [day_in_city[(d - 1) * len(cities) + cities.index(city)] for city in cities]))

# Add constraints for each city's stay
for city in cities:
    start = start_days[city]
    duration = stay_durations[city]
    for d in range(1, total_days + 1):
        for i in range(duration):
            solver.add(Implies(day_in_city[(d - 1) * len(cities) + cities.index(city)], start + i == d))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for d in range(1, total_days + 1):
        for city in cities:
            if model.evaluate(day_in_city[(d - 1) * len(cities) + cities.index(city)]):
                itinerary.append({'day': d, 'city': city})
                break
    print(json.dumps({'itinerary': itinerary}, indent=2))
else:
    print("No solution found")