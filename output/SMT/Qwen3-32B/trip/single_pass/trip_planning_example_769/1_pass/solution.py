import z3
import json

solver = z3.Solver()

# Create variables for each day (1-16), stored in a list with indexes 0-15
city = [z3.Int(f'city_{i}') for i in range(1, 17)]  # city[0] is day 1, ..., city[15] is day 16

allowed_flights = [
    (0,4), (4,0),  # Porto-Amsterdam
    (5,4), (4,5),  # Munich-Amsterdam
    (2,4), (4,2),  # Reykjavik-Amsterdam
    (5,0), (0,5),  # Munich-Porto
    (1,2), (2,1),  # Prague-Reykjavik
    (2,5), (5,2),  # Reykjavik-Munich
    (4,3), (3,4),  # Amsterdam-Santorini
    (1,4), (4,1),  # Prague-Amsterdam
    (1,5), (5,1),  # Prague-Munich
]

# Add constraints for consecutive flights
for j in range(0, 15):  # j ranges from 0 to 14 (days 1-15 and 2-16)
    a = city[j]
    b = city[j+1]
    allowed_expr = z3.Or([ z3.And(a == x, b == y) for (x, y) in allowed_flights ])
    solver.add(z3.Implies(a != b, allowed_expr))

# Add total days constraints
required_days = {0:5, 1:4, 2:4, 3:2, 4:2, 5:4}

for c in range(6):
    sum_days = sum(z3.If(city[j] == c, 1, 0) for j in range(0, 16))  # days 1-16
    arrivals = sum(z3.If(z3.And(city[j] != c, city[j+1] == c), 1, 0) for j in range(0, 15))  # transitions 1-15
    total_days = sum_days + arrivals
    solver.add(total_days == required_days[c])

# Amsterdam constraints: days 14 and 15 are Amsterdam (city[13] and city[14])
solver.add(city[13] == 4)
solver.add(city[14] == 4)

# All other days are not Amsterdam
for j in range(0, 16):
    if j != 13 and j != 14:  # days 14 and 15 are indexes 13 and 14
        solver.add(city[j] != 4)

# No transitions into Amsterdam except from Amsterdam
for j in range(0, 15):
    solver.add(z3.Implies(city[j+1] == 4, city[j] == 4))

# Reykjavik wedding constraint: days 4-7 (indexes 3,4,5,6)
solver.add(z3.Or(city[3] == 2, city[4] == 2, city[5] == 2, city[6] == 2))

# Munich meeting constraint: days 7-10 (indexes 6,7,8,9)
solver.add(z3.Or(city[6] == 5, city[7] == 5, city[8] == 5, city[9] == 5))

# Check if the problem is satisfiable
if solver.check() == z3.sat:
    model = solver.model()
    # Extract the itinerary
    itinerary = []
    city_names = {0: 'Porto', 1: 'Prague', 2: 'Reykjavik', 3: 'Santorini', 4: 'Amsterdam', 5: 'Munich'}
    for j in range(0, 16):  # days 1-16
        day = j + 1
        city_val = model.evaluate(city[j]).as_long()
        city_name = city_names[city_val]
        itinerary.append({'day': day, 'city': city_name})
    # Convert to JSON format
    json_output = {'itinerary': {entry['day']: entry['city'] for entry in itinerary}}
    print(json.dumps(json_output, indent=2))
else:
    print("No solution found.")