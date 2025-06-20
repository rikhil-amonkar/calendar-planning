from z3 import *

# Define the cities
cities = ['Paris', 'Oslo', 'Geneva', 'Porto', 'Reykjavik']

# Define the days
days = range(1, 24)

# Define the direct flights
flights = {
    'Paris': ['Oslo', 'Porto', 'Geneva'],
    'Oslo': ['Paris', 'Geneva', 'Reykjavik'],
    'Geneva': ['Oslo', 'Paris', 'Porto'],
    'Porto': ['Paris', 'Geneva', 'Oslo'],
    'Reykjavik': ['Oslo', 'Paris']
}

# Define the constraints
constraints = []
visit_days = {city: 0 for city in cities}
visit_days['Paris'] = 6
visit_days['Oslo'] = 5
visit_days['Geneva'] = 7
visit_days['Porto'] = 7
visit_days['Reykjavik'] = 2

for city in cities:
    for day in days:
        if day < visit_days[city]:
            constraints.append(Or([Bool(f'{city}_{day}')]))
        else:
            constraints.append(Not(Bool(f'{city}_{day}')))

for day in days:
    for city in cities:
        for flight in flights[city]:
            constraints.append(Not(And(Bool(f'{city}_{day}'), Bool(f'{flight}_{day}'))))

for day in days:
    if day == 1 or day == 7:
        constraints.append(Bool('Geneva_1'))
        constraints.append(Bool('Geneva_7'))
    if day >= 19 and day <= 23:
        constraints.append(Bool('Oslo_19'))
        constraints.append(Bool('Oslo_20'))
        constraints.append(Bool('Oslo_21'))
        constraints.append(Bool('Oslo_22'))
        constraints.append(Bool('Oslo_23'))

solver = Solver()
for constraint in constraints:
    solver.add(constraint)

if solver.check() == sat:
    model = solver.model()
    trip_plan = {}
    for city in cities:
        trip_plan[city] = []
        for day in days:
            if model.evaluate(Bool(f'{city}_{day}')).as_bool():
                trip_plan[city].append(day)
    for city, days in trip_plan.items():
        print(f'{city}: {days}')
else:
    print('No solution found')