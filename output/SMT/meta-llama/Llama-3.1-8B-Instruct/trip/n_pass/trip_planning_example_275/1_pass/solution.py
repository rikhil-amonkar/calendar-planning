from z3 import *

# Define the cities and their durations
cities = ['Split', 'Vilnius', 'Santorini', 'Madrid']
durations = {'Split': 5, 'Vilnius': 4, 'Santorini': 2, 'Madrid': 6}

# Define the direct flights
flights = [('Vilnius', 'Split'), ('Split', 'Madrid'), ('Madrid', 'Santorini')]

# Define the solver
solver = Solver()

# Define the variables
days = [Int(f'day_{i}') for i in range(15)]
in_city = [Bool(f'in_{city}') for city in cities]

# Add constraints
for day in days:
    # Each day is a non-negative integer
    solver.add(day >= 0)
    # Each day is less than 15
    solver.add(day < 15)
# Ensure that each city is visited for the correct number of days
for city, duration in durations.items():
    # Sum of days in this city is equal to the duration
    solver.add(ForAll([day], Implies(day >= duration, day <= duration + 1)))
    # The day after the last day in this city is 0
    solver.add(Implies(day == duration + 1, Not(in_city[cities.index(city)])))
# Ensure that you can only be in one city at a time
solver.add(Or(*[in_city[i] for i in range(len(cities))]))
# Ensure that you can only be in a city if you've arrived there
solver.add(Implies(in_city[cities.index('Split')], Or([day == 1 for day in days])))
solver.add(Implies(in_city[cities.index('Vilnius')], Or([day == 1 for day in days])))
solver.add(Implies(in_city[cities.index('Madrid')], Or([day == 1 for day in days]))))
solver.add(Implies(in_city[cities.index('Santorini')], Or([day == 12 for day in days]))))
# Ensure that you can only fly from one city to another if you're in the first city
for flight in flights:
    city1, city2 = flight
    solver.add(Implies(in_city[cities.index(city1)], Or([day == day1 + 1 for day1, day2 in zip(days, days[1:]) if day1 == durations[city1] and day2 == 0 and city2 == cities[day2]])))
# Ensure that you're in Santorini on day 13 and 14
solver.add(in_city[cities.index('Santorini')] == days[12] == days[13] == days[14] == 1)

# Check the solution
if solver.check() == sat:
    model = solver.model()
    print('Trip plan:')
    for day in days:
        print(f'Day {model[day].as_long()}:', end=' ')
        for city in cities:
            if model[in_city[cities.index(city)]].as_bool():
                print(city, end=' ')
        print()
else:
    print('No solution found')