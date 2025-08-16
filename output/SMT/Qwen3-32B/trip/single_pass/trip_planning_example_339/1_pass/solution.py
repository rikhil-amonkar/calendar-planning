from z3 import *
import json

# Initialize solver
solver = Solver()

# Define cities as integers: 0-Warsaw, 1-Budapest, 2-Paris, 3-Riga
cities = [Int(f'city_{i+1}') for i in range(17)]  # 17 days, day 1 to 17

# Constraint: Day 1 and 2 must be in Warsaw (0)
solver.add(cities[0] == 0)
solver.add(cities[1] == 0)

# Transition constraints: Forbidden transitions (1,3) and (3,1)
for i in range(16):
    current = cities[i]
    next_city = cities[i + 1]
    solver.add(Not(And(current == 1, next_city == 3)))
    solver.add(Not(And(current == 3, next_city == 1)))

# Calculate total days for each city
total_days = [0, 0, 0, 0]  # For cities 0-3
for c in range(4):
    sum1 = Sum([If(cities[i] == c, 1, 0) for i in range(17)])
    sum2 = Sum([If(And(cities[i + 1] == c, cities[i] != c), 1, 0) for i in range(16)])
    total_days[c] = sum1 + sum2

# Add constraints for total days in each city
solver.add(total_days[0] == 2)  # Warsaw
solver.add(total_days[1] == 7)  # Budapest
solver.add(total_days[2] == 4)  # Paris
solver.add(total_days[3] == 7)  # Riga

# Ensure Riga has at least one day between day 11 and 17 (indices 10 to 16)
riga_days = [cities[i] == 3 for i in range(10, 17)]
solver.add(Or(riga_days))

# Check for solution
if solver.check() == sat:
    model = solver.model()
    # Build itinerary
    itinerary = []
    city_names = {0: 'Warsaw', 1: 'Budapest', 2: 'Paris', 3: 'Riga'}
    for i in range(17):
        day = i + 1
        city_code = model.evaluate(cities[i]).as_long()
        city_name = city_names[city_code]
        itinerary.append({day: city_name})
    # Output JSON
    print(json.dumps({'itinerary': itinerary}))
else:
    print("No solution found.")