from z3 import *

# Define the cities
cities = ['Helsinki', 'Prague', 'Valencia', 'Porto', 'Dubrovnik', 'Reykjavik']

# Define the durations of stay in each city
durations = {'Helsinki': 4, 'Prague': 3, 'Valencia': 5, 'Porto': 3, 'Dubrovnik': 4, 'Reykjavik': 4}

# Define the direct flights
flights = {'Helsinki': ['Prague', 'Reykjavik'], 'Prague': ['Helsinki', 'Valencia'], 'Valencia': ['Prague', 'Porto'], 
           'Dubrovnik': ['Helsinki'], 'Reykjavik': ['Helsinki', 'Prague'], 'Porto': ['Valencia']}

# Define the variables for the days of stay in each city
days = [Int(f'city_{i}_day') for i in range(len(cities))]

# Define the total number of days
total_days = Int('total_days')
s = Solver()
for i, city in enumerate(cities):
    s.add(days[i] >= durations[city])
    s.add(days[i] >= 0)

s.add(Or([days[i] == 0 for i in range(len(cities))]))
s.add(total_days == 18)

# Meet the friend in Porto between day 16 and day 18
s.add(days[3] >= 16)
s.add(days[3] <= 18)

# Direct flights
for city in cities:
    if city in flights:
        for destination in flights[city]:
            idx = cities.index(destination)
            s.add(days[cities.index(city)] + 1 == days[idx])

# Check the constraints
if s.check() == sat:
    model = s.model()
    # Print the solution
    print('Day\tHelsinki\tPrague\tValencia\tPorto\tDubrovnik\tReykjavik')
    for i in range(18):
        day = i + 1
        print(f'{day}\t{model[days[0]].as_long()}\t{model[days[1]].as_long()}\t{model[days[2]].as_long()}\t{model[days[3]].as_long()}\t{model[days[4]].as_long()}\t{model[days[5]].as_long()}')
else:
    print('No solution found')