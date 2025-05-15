from z3 import *

# Define the cities and their durations
cities = ['Santorini', 'Krakow', 'Paris', 'Vilnius', 'Munich', 'Geneva', 'Amsterdam', 'Budapest', 'Split']
durations = {
    'Santorini': 5,
    'Krakow': 5,
    'Paris': 5,
    'Vilnius': 3,
    'Munich': 5,
    'Geneva': 2,
    'Amsterdam': 4,
    'Budapest': 5,
    'Split': 4
}

# Define direct flights between cities
flights = {
    'Paris': ['Krakow', 'Amsterdam', 'Split'],
    'Vilnius': ['Munich'],
    'Munich': ['Split', 'Amsterdam', 'Geneva', 'Krakow', 'Budapest', 'Paris'],
    'Geneva': [],
    'Amsterdam': ['Geneva', 'Santorini'],
    'Budapest': ['Amsterdam', 'Paris'],
    'Split': ['Krakow', 'Geneva', 'Amsterdam'],
    'Krakow': ['Vilnius', 'Amsterdam'],
    'Santorini': []
}

# Create variables for each city's start and end days
start = {city: Int(city + '_start') for city in cities}
end = {city: Int(city + '_end') for city in cities}

# Create solver
solver = Solver()

# Add duration constraints for each city
for city in cities:
    solver.add(end[city] == start[city] + durations[city] - 1)

# Add fixed constraints for specific events
solver.add(start['Santorini'] >= 25)
solver.add(end['Santorini'] <= 29)
solver.add(start['Krakow'] >= 18)
solver.add(end['Krakow'] <= 22)
solver.add(start['Paris'] >= 11)
solver.add(end['Paris'] <= 15)

# Ensure the entire trip covers exactly 30 days
solver.add(end['Santorini'] == 30)

# Create 'next' variables to model the sequence of cities
next_city = {city: String(city + '_next') for city in cities}

# Each city must have a next city that is different
for city in cities:
    solver.add(Or([next_city[city] == c for c in cities if c != city]))

# For each possible pair of cities (A, B), if B is the next city after A,
# then A's end day must be B's start day, and there must be a flight from A to B
for a in cities:
    for b in cities:
        if a == b:
            continue
        solver.add(
            Implies(
                next_city[a] == b,
                And(
                    end[a] == start[b],
                    b in flights.get(a, [])
                )
            )
        )

# Ensure that the sequence starts with Paris and ends with Santorini
solver.add(next_city['Paris'] != 'Paris')  # Paris is not the last city
solver.add(next_city['Santorini'] == 'Santorini')  # Santorini has no next city

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    itinerary = []
    current_city = 'Paris'
    while current_city != 'Santorini':
        next_c = model[next_city[current_city]]
        itinerary.append((current_city, model[start[current_city]], model[end[current_city]]))
        current_city = next_c
    itinerary.append((current_city, model[start[current_city]], model[end[current_city]]))
    
    for city_info in itinerary:
        print(f"City: {city_info[0]}, Start Day: {city_info[1]}, End Day: {city_info[2]}")
else:
    print("No solution found.")