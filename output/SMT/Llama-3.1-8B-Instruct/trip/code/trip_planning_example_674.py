from z3 import *

# Define the cities
cities = ['Helsinki', 'Warsaw', 'Madrid', 'Split', 'Reykjavik', 'Budapest']

# Define the days
days = range(1, 15)

# Define the direct flights
flights = {
    ('Helsinki', 'Reykjavik'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
    ('Budapest', 'Warsaw'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
    ('Madrid', 'Split'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
    ('Helsinki', 'Split'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
    ('Helsinki', 'Madrid'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
    ('Helsinki', 'Budapest'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
    ('Reykjavik', 'Warsaw'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
    ('Helsinki', 'Warsaw'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
    ('Madrid', 'Budapest'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
    ('Budapest', 'Reykjavik'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
    ('Madrid', 'Warsaw'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
    ('Warsaw', 'Split'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
    ('Reykjavik', 'Madrid'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
}

# Define the constraints
solver = Solver()

# Define the variables
x = {city: [Bool(f'{city}_day_{day}') for day in days] for city in cities}

# Constraints for workshop
for day in [1, 2]:
    solver.add(Not(x['Helsinki'][day]))

# Constraints for visiting relatives
for day in [9, 10, 11]:
    solver.add(Not(x['Warsaw'][day]))

# Constraints for staying in each city
for city in cities:
    for day in days:
        if city == 'Helsinki' and (day >= 1 and day <= 2):
            solver.add(x[city][day])
        elif city == 'Warsaw' and (day >= 1 and day <= 3):
            solver.add(x[city][day])
        elif city == 'Madrid' and (day >= 1 and day <= 4):
            solver.add(x[city][day])
        elif city == 'Split' and (day >= 1 and day <= 4):
            solver.add(x[city][day])
        elif city == 'Reykjavik' and (day >= 1 and day <= 2):
            solver.add(x[city][day])
        elif city == 'Budapest' and (day >= 1 and day <= 4):
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