from z3 import *

# Define the cities
cities = ['Helsinki', 'Prague', 'Valencia', 'Porto', 'Dubrovnik', 'Reykjavik']

# Define the durations of stay in each city
durations = {'Helsinki': 4, 'Valencia': 5, 'Dubrovnik': 4, 'Porto': 3, 'Prague': 3, 'Reykjavik': 4}

# Define the direct flights
flights = {'Helsinki': ['Prague', 'Reykjavik'], 'Prague': ['Helsinki', 'Valencia'], 'Valencia': ['Prague', 'Porto'], 
           'Dubrovnik': ['Helsinki'], 'Reykjavik': ['Helsinki', 'Prague']}

# Define the variables for the days of stay in each city
days = [Int(f'{city}_day') for city in cities]

# Define the constraints
s = Solver()
for city in cities:
    s.add(days[city] >= durations[city])
    s.add(days[city] >= 0)

s.add(days['Helsinki'] + days['Prague'] + days['Valencia'] + days['Porto'] + days['Dubrovnik'] + days['Reykjavik'] == 18)

# Meet the friend in Porto between day 16 and day 18
s.add(days['Porto'] >= 16)
s.add(days['Porto'] <= 18)

# Direct flights
for city in cities:
    for destination in flights[city]:
        s.add(days[city] + 1 == days[destination])

# Solve the constraints
s.check()
model = s.model()

# Print the solution
print('Day\tHelsinki\tPrague\tValencia\tPorto\tDubrovnik\tReykjavik')
for i in range(18):
    day = i + 1
    print(f'{day}\t{model[days["Helsinki"]].as_long()}\t{model[days["Prague"]].as_long()}\t{model[days["Valencia"]].as_long()}\t{model[days["Porto"]].as_long()}\t{model[days["Dubrovnik"]].as_long()}\t{model[days["Reykjavik"]].as_long()}')