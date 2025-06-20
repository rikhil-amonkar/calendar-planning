from z3 import *

# Define the cities
cities = ['Helsinki', 'Prague', 'Valencia', 'Porto', 'Dubrovnik', 'Reykjavik']

# Define the durations of stay in each city
durations = {'Helsinki': 4, 'Prague': 3, 'Valencia': 5, 'Porto': 3, 'Dubrovnik': 4, 'Reykjavik': 4}

# Define the direct flights
flights = {'Helsinki': ['Prague', 'Reykjavik'], 'Prague': ['Helsinki', 'Valencia'], 'Valencia': ['Prague', 'Porto'], 
           'Dubrovnik': ['Helsinki'], 'Reykjavik': ['Helsinki', 'Prague']}

# Define the variables for the days of stay in each city
days = [Int(f'{city}_day') for city in cities]

# Define the total number of days
total_days = Int('total_days')
s = Solver()
for city in cities:
    s.add(days[city] >= durations[city])
    s.add(days[city] >= 0)

s.add(total_days == 18)

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