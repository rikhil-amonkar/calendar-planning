from z3 import *

# Define the variables
days = 30
cities = ['Santorini', 'Krakow', 'Paris', 'Vilnius', 'Munich', 'Geneva', 'Amsterdam', 'Budapest', 'Split']
flight_connections = {
    'Paris': ['Krakow', 'Amsterdam', 'Split', 'Geneva'],
    'Krakow': ['Paris', 'Amsterdam', 'Split', 'Munich', 'Vilnius'],
    'Vilnius': ['Munich', 'Amsterdam', 'Krakow', 'Split'],
    'Munich': ['Vilnius', 'Amsterdam', 'Geneva', 'Split', 'Krakow', 'Budapest'],
    'Geneva': ['Paris', 'Amsterdam', 'Munich', 'Split', 'Budapest'],
    'Amsterdam': ['Paris', 'Split', 'Geneva', 'Vilnius', 'Krakow', 'Budapest', 'Santorini'],
    'Budapest': ['Paris', 'Geneva', 'Munich', 'Amsterdam'],
    'Split': ['Paris', 'Amsterdam', 'Geneva', 'Krakow', 'Munich', 'Vilnius'],
    'Santorini': ['Geneva', 'Amsterdam']
}
santorini_days = 5
krakow_days = 5
paris_days = 5
vilnius_days = 3
munich_days = 5
geneva_days = 2
amsterdam_days = 4
budapest_days = 5
split_days = 4
wedding_days = 5
friend_days = 5

# Create the solver
solver = Solver()

# Define the variables
x = [Int(f'{city}_day') for city in cities]
y = [Int(f'{city}_day2') for city in cities]

# Define the constraints
for city in cities:
    solver.add(x[city] >= 1)
    solver.add(x[city] <= days)
    solver.add(y[city] >= 1)
    solver.add(y[city] <= days)

solver.add(x['Santorini'] >= santorini_days)
solver.add(x['Santorini'] <= days)
solver.add(x['Krakow'] >= wedding_days)
solver.add(x['Krakow'] <= days - wedding_days + 1)
solver.add(x['Paris'] >= friend_days)
solver.add(x['Paris'] <= days - friend_days + 1)
solver.add(x['Vilnius'] >= vilnius_days)
solver.add(x['Vilnius'] <= days)
solver.add(x['Munich'] >= munich_days)
solver.add(x['Munich'] <= days)
solver.add(x['Geneva'] >= geneva_days)
solver.add(x['Geneva'] <= days)
solver.add(x['Amsterdam'] >= amsterdam_days)
solver.add(x['Amsterdam'] <= days)
solver.add(x['Budapest'] >= budapest_days)
solver.add(x['Budapest'] <= days)
solver.add(x['Split'] >= split_days)
solver.add(x['Split'] <= days)

for city in cities:
    for other_city in flight_connections[city]:
        solver.add(Or([x[city] + 1 == x[other_city], y[city] + 1 == y[other_city]]))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    trip_plan = {}
    for city in cities:
        trip_plan[city] = model.evaluate(x[city]).as_long()
    for city in cities:
        trip_plan[city] += model.evaluate(y[city]).as_long()
        trip_plan[city] -= 1
    for city in cities:
        print(f'{city}: {trip_plan[city]}')
else:
    print('No solution found')