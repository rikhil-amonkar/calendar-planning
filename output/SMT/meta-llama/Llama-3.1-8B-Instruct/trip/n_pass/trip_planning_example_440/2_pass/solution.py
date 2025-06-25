from z3 import *
from itertools import product

# Define the cities
cities = ['Split', 'Helsinki', 'Reykjavik', 'Vilnius', 'Geneva']

# Define the days
days = range(1, 13)

# Define the direct flights
flights = [
    ('Split', 'Helsinki'),
    ('Geneva', 'Split'),
    ('Geneva', 'Helsinki'),
    ('Helsinki', 'Reykjavik'),
    ('Vilnius', 'Helsinki'),
    ('Split', 'Vilnius')
]

# Create the solver
s = Solver()

# Create the variables
itinerary = {}
for city in cities:
    itinerary[city] = [Bool(f'{city}_day_{day}') for day in days]

# Create the constraints
for city in cities:
    # Each city is visited for the specified number of days
    s.add(Or(*[itinerary[city][day-1] for day in range(1, len(itinerary[city])+1)]))
    s.add(And(*[itinerary[city][day-1] for day in range(1, len(itinerary[city])+1)]))

# Geneva is visited for 6 days
s.add(Or(*[itinerary['Geneva'][day-1] for day in range(1, 7)]))
s.add(And(*[itinerary['Geneva'][day-1] for day in range(1, 7)]))

# Split is visited for 2 days
s.add(Or(*[itinerary['Split'][day-1] for day in range(1, 3)]))
s.add(And(*[itinerary['Split'][day-1] for day in range(1, 3)]))

# Helsinki is visited for 2 days
s.add(Or(*[itinerary['Helsinki'][day-1] for day in range(1, 3)]))
s.add(And(*[itinerary['Helsinki'][day-1] for day in range(1, 3)]))

# Reykjavik is visited for 3 days
s.add(Or(*[itinerary['Reykjavik'][day-1] for day in range(1, 4)]))
s.add(And(*[itinerary['Reykjavik'][day-1] for day in range(1, 4)]))

# Vilnius is visited for 3 days
s.add(Or(*[itinerary['Vilnius'][day-1] for day in range(1, 4)]))
s.add(And(*[itinerary['Vilnius'][day-1] for day in range(1, 4)]))

# Wedding in Reykjavik between day 10 and day 12
s.add(And(itinerary['Reykjavik'][9], itinerary['Reykjavik'][10], itinerary['Reykjavik'][11]))

# Relatives in Vilnius between day 7 and day 9
s.add(And(itinerary['Vilnius'][6], itinerary['Vilnius'][7], itinerary['Vilnius'][8]))

# Direct flights
for departure, arrival in flights:
    for day in days:
        s.add(Implies(itinerary[departure][day-1], itinerary[arrival][day-1]))

# Solve the constraints
if s.check() == sat:
    model = s.model()
    itinerary_dict = {}
    for city in cities:
        itinerary_dict[city] = []
        for day in days:
            if model.evaluate(itinerary[city][day-1]).decl().name():
                itinerary_dict[city].append(f'Day {day}')
    for city in cities:
        if itinerary_dict[city]:
            if itinerary_dict[city][0] == 'Day 1':
                itinerary_dict[city] = [f'Day {min(itinerary_dict[city])}-{max(itinerary_dict[city])}']
            else:
                itinerary_dict[city] = [f'Day {min(itinerary_dict[city])}-{max(itinerary_dict[city])}']
    itinerary_dict['itinerary'] = []
    for city in cities:
        itinerary_dict['itinerary'].extend(itinerary_dict[city])
    print(itinerary_dict)
else:
    print('No solution found')