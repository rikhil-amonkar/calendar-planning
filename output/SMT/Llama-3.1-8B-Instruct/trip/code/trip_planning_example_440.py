from z3 import *

# Define the cities
cities = ['Split', 'Helsinki', 'Reykjavik', 'Vilnius', 'Geneva']

# Define the days
days = range(1, 13)

# Define the direct flights
flights = {
    ('Split', 'Helsinki'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
    ('Geneva', 'Split'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
    ('Geneva', 'Helsinki'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
    ('Helsinki', 'Reykjavik'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
    ('Vilnius', 'Helsinki'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
    ('Split', 'Vilnius'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
}

# Define the constraints
solver = Solver()

# Define the variables
x = {city: [Bool(f'{city}_day_{day}') for day in days] for city in cities}

# Constraints for wedding
for day in [10, 11, 12]:
    solver.add(Not(x['Reykjavik'][day]))

# Constraints for visiting relatives
for day in [7, 8, 9]:
    solver.add(Not(x['Vilnius'][day]))

# Constraints for staying in each city
for city in cities:
    for day in days:
        if city == 'Split' and (day >= 1 and day <= 2):
            solver.add(x[city][day])
        elif city == 'Helsinki' and (day >= 1 and day <= 2):
            solver.add(x[city][day])
        elif city == 'Reykjavik' and (day >= 1 and day <= 3):
            solver.add(x[city][day])
        elif city == 'Vilnius' and (day >= 1 and day <= 3):
            solver.add(x[city][day])
        elif city == 'Geneva' and (day >= 1 and day <= 6):
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