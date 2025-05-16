from z3 import *

# Define the cities
cities = ['Dublin', 'Helsinki', 'Riga', 'Reykjavik', 'Vienna', 'Tallinn']

# Define the days
days = range(1, 16)

# Define the direct flights
flights = {
    ('Helsinki', 'Riga'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ('Riga', 'Tallinn'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ('Vienna', 'Helsinki'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ('Riga', 'Dublin'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ('Vienna', 'Riga'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ('Reykjavik', 'Vienna'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ('Helsinki', 'Dublin'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ('Tallinn', 'Dublin'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ('Reykjavik', 'Helsinki'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ('Reykjavik', 'Dublin'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ('Helsinki', 'Tallinn'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ('Vienna', 'Dublin'): [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
}

# Define the constraints
solver = Solver()

# Define the variables
x = {city: [Bool(f'{city}_day_{day}') for day in days] for city in cities}

# Constraints for meeting friends
for day in [3, 4, 5]:
    solver.add(Not(x['Helsinki'][day]))

# Constraints for visiting relatives
for day in [7, 8, 9, 10, 11]:
    solver.add(Not(x['Tallinn'][day]))

# Constraints for staying in each city
for city in cities:
    for day in days:
        if city == 'Dublin' and (day >= 1 and day <= 5):
            solver.add(x[city][day])
        elif city == 'Helsinki' and (day >= 1 and day <= 3):
            solver.add(x[city][day])
        elif city == 'Riga' and (day >= 1 and day <= 3):
            solver.add(x[city][day])
        elif city == 'Reykjavik' and (day >= 1 and day <= 2):
            solver.add(x[city][day])
        elif city == 'Vienna' and (day >= 1 and day <= 2):
            solver.add(x[city][day])
        elif city == 'Tallinn' and (day >= 1 and day <= 5):
            solver.add(x[city][day])

# Constraints for annual show
for day in [2, 3]:
    solver.add(Not(x['Vienna'][day]))

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