from z3 import *

# Define the cities and their durations
cities = ['Santorini', 'Valencia', 'Madrid', 'Seville', 'Bucharest', 'Vienna', 'Riga', 'Tallinn', 'Krakow', 'Frankfurt']
durations = {
    'Santorini': 3,
    'Valencia': 4,
    'Madrid': 2,
    'Seville': 2,
    'Bucharest': 3,
    'Vienna': 4,
    'Riga': 4,
    'Tallinn': 5,
    'Krakow': 5,
    'Frankfurt': 4
}

# Define direct flights between cities
flights = {
    'Vienna': ['Bucharest', 'Seville', 'Valencia', 'Madrid', 'Krakow', 'Frankfurt', 'Riga'],
    'Santorini': ['Madrid', 'Bucharest'],
    'Seville': ['Valencia'],
    'Madrid': ['Valencia', 'Seville', 'Bucharest', 'Frankfurt'],
    'Bucharest': ['Riga', 'Valencia', 'Santorini'],
    'Valencia': ['Bucharest', 'Krakow', 'Frankfurt'],
    'Riga': ['Tallinn'],
    'Tallinn': [],
    'Krakow': ['Frankfurt'],
    'Frankfurt': ['Tallinn', 'Bucharest', 'Riga']
}

# Create variables for each city's start and end days
start = {city: Int(city + '_start') for city in cities}
end = {city: Int(city + '_end') for city in cities}

# Create solver
solver = Solver()

# Add duration constraints for each city
for city in cities:
    solver.add(end[city] == start[city] + durations[city] - 1)

# Add constraints for the entire trip duration
for city in cities:
    solver.add(start[city] >= 1)
    solver.add(end[city] <= 27)

# Add fixed constraints for specific events
solver.add(start['Vienna'] >= 3)
solver.add(end['Vienna'] <= 6)
solver.add(start['Riga'] >= 20)
solver.add(end['Riga'] <= 23)
solver.add(start['Tallinn'] >= 23)
solver.add(end['Tallinn'] <= 27)
solver.add(start['Krakow'] >= 11)
solver.add(end['Krakow'] <= 15)

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

# Ensure that the sequence starts with Vienna and ends with Tallinn
solver.add(next_city['Vienna'] != 'Vienna')  # Vienna is not the last city
solver.add(next_city['Tallinn'] == 'Tallinn')  # Tallinn has no next city

# Solve the problem
result = solver.check()

if result == sat:
    model = solver.model()
    itinerary = []
    current_city = 'Vienna'
    while current_city != 'Tallinn':
        next_c = model[next_city[current_city]]
        itinerary.append((current_city, model[start[current_city]], model[end[current_city]]))
        current_city = next_c
    itinerary.append((current_city, model[start[current_city]], model[end[current_city]]))
    
    for city_info in itinerary:
        print(f"City: {city_info[0]}, Start Day: {city_info[1]}, End Day: {city_info[2]}")
else:
    print("No solution found.")