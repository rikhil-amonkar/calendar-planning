from z3 import *

# Define the cities
cities = ['Paris', 'Madrid', 'Bucharest', 'Seville']

# Define the days
days = range(1, 16)

# Define the direct flights
flights = {
    ('Paris', 'Bucharest'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ('Seville', 'Paris'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ('Madrid', 'Bucharest'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ('Madrid', 'Paris'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ('Madrid', 'Seville'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
}

# Define the constraints
solver = Solver()

# Define the variables
x = {city: [Bool(f'{city}_day_{day}') for day in days] for city in cities}

# Constraints for annual show
for day in range(1, 8):
    solver.add(Not(x['Madrid'][day]))

# Constraints for visiting relatives
for day in [14, 15]:
    solver.add(Not(x['Bucharest'][day]))

# Constraints for staying in each city
for city in cities:
    for day in days:
        if city == 'Paris' and (day >= 1 and day <= 6):
            solver.add(x[city][day])
        elif city == 'Madrid' and (day >= 1 and day <= 7):
            solver.add(x[city][day])
        elif city == 'Bucharest' and (day >= 1 and day <= 2):
            solver.add(x[city][day])
        elif city == 'Seville' and (day >= 1 and day <= 3):
            solver.add(x[city][day])

# Constraints for direct flights
for (city1, city2), days in flights.items():
    for day in days:
        solver.add(Implies(x[city1][day], x[city2][day]))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    trip_plan = {}
    for city in cities:
        trip_plan[city] = []
        for day in days:
            if model[x[city][day]]:
                trip_plan[city].append(day)
    print(trip_plan)
else:
    print("No solution exists")