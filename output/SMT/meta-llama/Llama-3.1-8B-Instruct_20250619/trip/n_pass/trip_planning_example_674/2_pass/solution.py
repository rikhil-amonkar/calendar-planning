from z3 import *

# Define the variables
days = 14
cities = ['Helsinki', 'Reykjavik', 'Budapest', 'Warsaw', 'Madrid', 'Split']
num_days_in_city = {city: 0 for city in cities}
days_in_trip = [0] * days

# Create a variable for each city and day
for city in cities:
    num_days_in_city[city] = Int(city)
for i in range(days):
    days_in_trip[i] = Int(f'day_{i}')

# Constraints
# Total days constraint
total_days = Sum([num_days_in_city[city] for city in cities])
total_days == days

# Each city must be visited for at least 0 days
for city in cities:
    num_days_in_city[city] >= 0

# Constraints for specific city stays
num_days_in_city['Helsinki'] == 2
num_days_in_city['Warsaw'] == 3
num_days_in_city['Madrid'] == 4
num_days_in_city['Split'] == 4
num_days_in_city['Reykjavik'] == 2

# Constraints for workshop and relative visits
num_days_in_city['Helsinki'] >= 1  # Workshop
num_days_in_city['Helsinki'] >= 2  # Stay
num_days_in_city['Warsaw'] >= 9  # Relative visit
num_days_in_city['Warsaw'] >= 11  # Relative visit
num_days_in_city['Reykjavik'] >= 8  # Friend visit
num_days_in_city['Reykjavik'] >= 9  # Friend visit

# Constraints for direct flights
# Helsinki and Reykjavik
num_days_in_city['Helsinki'] >= days_in_trip[0] - 1
num_days_in_city['Reykjavik'] >= days_in_trip[0] - 1
# Budapest and Warsaw
num_days_in_city['Budapest'] >= days_in_trip[9] - 1
num_days_in_city['Warsaw'] >= days_in_trip[9] - 1
# Madrid and Split
num_days_in_city['Madrid'] >= days_in_trip[10] - 1
num_days_in_city['Split'] >= days_in_trip[10] - 1
# Helsinki and Split
num_days_in_city['Helsinki'] >= days_in_trip[1] - 1
num_days_in_city['Split'] >= days_in_trip[1] - 1
# Helsinki and Madrid
num_days_in_city['Helsinki'] >= days_in_trip[2] - 1
num_days_in_city['Madrid'] >= days_in_trip[2] - 1
# Helsinki and Budapest
num_days_in_city['Helsinki'] >= days_in_trip[3] - 1
num_days_in_city['Budapest'] >= days_in_trip[3] - 1
# Reykjavik and Warsaw
num_days_in_city['Reykjavik'] >= days_in_trip[7] - 1
num_days_in_city['Warsaw'] >= days_in_trip[7] - 1
# Helsinki and Warsaw
num_days_in_city['Helsinki'] >= days_in_trip[4] - 1
num_days_in_city['Warsaw'] >= days_in_trip[4] - 1
# Madrid and Budapest
num_days_in_city['Madrid'] >= days_in_trip[5] - 1
num_days_in_city['Budapest'] >= days_in_trip[5] - 1
# Budapest and Reykjavik
num_days_in_city['Budapest'] >= days_in_trip[6] - 1
num_days_in_city['Reykjavik'] >= days_in_trip[6] - 1
# Madrid and Warsaw
num_days_in_city['Madrid'] >= days_in_trip[8] - 1
num_days_in_city['Warsaw'] >= days_in_trip[8] - 1
# Warsaw and Split
num_days_in_city['Warsaw'] >= days_in_trip[12] - 1
num_days_in_city['Split'] >= days_in_trip[12] - 1
# Reykjavik and Madrid
num_days_in_city['Reykjavik'] >= days_in_trip[11] - 1
num_days_in_city['Madrid'] >= days_in_trip[11] - 1

# Constraints for days in trip
for i in range(days):
    days_in_trip[i] == Sum([num_days_in_city[city] for city in cities if i == 0 and city == 'Helsinki' or i == 1 and city == 'Reykjavik' or i == 2 and city == 'Madrid' or i == 3 and city == 'Budapest' or i == 4 and city == 'Warsaw' or i == 5 and city == 'Madrid' or i == 6 and city == 'Budapest' or i == 7 and city == 'Warsaw' or i == 8 and city == 'Madrid' or i == 9 and city == 'Budapest' or i == 10 and city == 'Madrid' or i == 11 and city == 'Reykjavik' or i == 12 and city == 'Warsaw' or i == 13 and city == 'Split' or i == 0 and city == 'Reykjavik'])

# Constraints for days in trip
for i in range(days):
    days_in_trip[i] >= 0
    if i == 0:
        days_in_trip[i] == 1
    elif i == 1:
        days_in_trip[i] == 1
    elif i == 2:
        days_in_trip[i] == 1
    elif i == 3:
        days_in_trip[i] == 1
    elif i == 4:
        days_in_trip[i] == 1
    elif i == 5:
        days_in_trip[i] == 1
    elif i == 6:
        days_in_trip[i] == 1
    elif i == 7:
        days_in_trip[i] == 1
    elif i == 8:
        days_in_trip[i] == 1
    elif i == 9:
        days_in_trip[i] == 1
    elif i == 10:
        days_in_trip[i] == 1
    elif i == 11:
        days_in_trip[i] == 1
    elif i == 12:
        days_in_trip[i] == 1
    elif i == 13:
        days_in_trip[i] == 1
    elif i == 14:
        days_in_trip[i] == 0

# Solve the problem
solver = Solver()
solver.add([num_days_in_city[city] >= 0 for city in cities])
solver.add([days_in_trip[i] >= 0 for i in range(days)])
solver.add([days_in_trip[i] <= 1 for i in range(days)])
solver.add([days_in_trip[0] == 1])
solver.add([days_in_trip[1] == 1])
solver.add([days_in_trip[2] == 1])
solver.add([days_in_trip[3] == 1])
solver.add([days_in_trip[4] == 1])
solver.add([days_in_trip[5] == 1])
solver.add([days_in_trip[6] == 1])
solver.add([days_in_trip[7] == 1])
solver.add([days_in_trip[8] == 1])
solver.add([days_in_trip[9] == 1])
solver.add([days_in_trip[10] == 1])
solver.add([days_in_trip[11] == 1])
solver.add([days_in_trip[12] == 1])
solver.add([days_in_trip[13] == 1])
solver.add([days_in_trip[14] == 0])
for city in cities:
    solver.add(num_days_in_city[city] == 2)
    solver.add(num_days_in_city[city] == 3)
    solver.add(num_days_in_city[city] == 4)
solver.add(total_days == days)

if solver.check() == sat:
    model = solver.model()
    for city in cities:
        print(f"{city}: {model[num_days_in_city[city]]}")
    for i in range(days):
        print(f"Day {i+1}: {model[days_in_trip[i]]}")
else:
    print("No solution found")