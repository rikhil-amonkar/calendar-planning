from z3 import *

# Define the cities
cities = ['Warsaw', 'Budapest', 'Riga', 'Paris']

# Define the number of days in each city
days_in_city = {'Warsaw': 2, 'Budapest': 7, 'Riga': 7, 'Paris': 4}

# Define the direct flights
flights = [('Warsaw', 'Budapest'), ('Warsaw', 'Riga'), ('Budapest', 'Paris'), 
           ('Warsaw', 'Paris'), ('Paris', 'Riga')]

# Define the constraints
n = 17  # total number of days
x = {city: [Bool(f'{city}_day_{i}') for i in range(1, n+1)] for city in cities}

# Each city is visited for a certain number of days
for city in cities:
    for i in range(1, days_in_city[city]+1):
        x[city][i-1] = True

# Wedding in Riga between day 11 and day 17
for i in range(11, 18):
    x['Riga'][i-1] = True

# Each day, exactly one city is visited
for day in range(1, n+1):
    c = [x[city][day-1] for city in cities]
    solution = solve(Or([Not(a) for a in c]))
    for city in cities:
        x[city][day-1] = solution.eval(x[city][day-1])

# Direct flights
for city1, city2 in flights:
    for day in range(1, n+1):
        if day > days_in_city[city1] and day <= days_in_city[city2]:
            c = x[city1][day-1] == x[city2][day-1]
            solve(c)

# Print the solution
for day in range(1, n+1):
    for city in cities:
        if x[city][day-1]:
            print(f'Day {day}: {city}')