import json
from z3 import *

# Define cities and their indexes
cities = ['Paris', 'Warsaw', 'Krakow', 'Tallinn', 'Riga', 'Copenhagen', 'Helsinki', 'Oslo', 'Santorini', 'Lyon']
durations = [5, 2, 2, 2, 2, 5, 5, 5, 2, 4]

# Define allowed flights
allowed_flights = set()
allowed_flights.add((1, 4))
allowed_flights.add((4, 1))
allowed_flights.add((1, 3))
allowed_flights.add((3, 1))
allowed_flights.add((5, 6))
allowed_flights.add((6, 5))
allowed_flights.add((9, 0))
allowed_flights.add((0, 9))
allowed_flights.add((5, 1))
allowed_flights.add((1, 5))
allowed_flights.add((9, 7))
allowed_flights.add((7, 9))
allowed_flights.add((0, 7))
allowed_flights.add((7, 0))
allowed_flights.add((0, 4))
allowed_flights.add((4, 0))
allowed_flights.add((2, 6))
allowed_flights.add((6, 2))
allowed_flights.add((0, 3))
allowed_flights.add((3, 0))
allowed_flights.add((7, 4))
allowed_flights.add((4, 7))
allowed_flights.add((2, 1))
allowed_flights.add((1, 2))
allowed_flights.add((0, 6))
allowed_flights.add((6, 0))
allowed_flights.add((5, 8))
allowed_flights.add((8, 5))
allowed_flights.add((6, 1))
allowed_flights.add((1, 6))
allowed_flights.add((6, 4))
allowed_flights.add((4, 6))
allowed_flights.add((5, 2))
allowed_flights.add((2, 5))
allowed_flights.add((5, 4))
allowed_flights.add((4, 5))
allowed_flights.add((0, 2))
allowed_flights.add((2, 0))
allowed_flights.add((5, 7))
allowed_flights.add((7, 5))
allowed_flights.add((7, 3))
allowed_flights.add((3, 7))
allowed_flights.add((7, 6))
allowed_flights.add((6, 7))
allowed_flights.add((5, 3))
allowed_flights.add((3, 5))
allowed_flights.add((7, 2))
allowed_flights.add((2, 7))
allowed_flights.add((4, 3))
allowed_flights.add((3, 4))
allowed_flights.add((6, 3))
allowed_flights.add((3, 6))
allowed_flights.add((0, 5))
allowed_flights.add((5, 0))
allowed_flights.add((0, 1))
allowed_flights.add((1, 0))
allowed_flights.add((8, 7))
allowed_flights.add((7, 8))
allowed_flights.add((7, 1))
allowed_flights.add((1, 7))

# Create Z3 solver
solver = Solver()

# Create order variables
order = [Int(f'order_{i}') for i in range(10)]
solver.add(Distinct(order))
for i in range(10):
    solver.add(And(order[i] >= 0, order[i] <= 9))

# Create start_day and end_day variables
start_day = [Int(f'start_day_{i}') for i in range(10)]
end_day = [Int(f'end_day_{i}') for i in range(10)]

# Add constraints for start_day and end_day
solver.add(start_day[0] == 1)
for i in range(1, 10):
    solver.add(start_day[i] == end_day[i-1])

# Add duration constraints
for i in range(10):
    expr = 0
    for j in range(10):
        expr = If(order[i] == j, durations[j], expr)
    solver.add(end_day[i] == start_day[i] + expr - 1)

# Add specific day constraints
for i in range(10):
    # Paris (index 0): days 4-8
    solver.add(Implies(order[i] == 0, And(start_day[i] == 4, end_day[i] == 8)))
    # Santorini (index 8): days 12-13
    solver.add(Implies(order[i] == 8, And(start_day[i] == 12, end_day[i] == 13)))
    # Krakow (index 2): days 17-18
    solver.add(Implies(order[i] == 2, And(start_day[i] == 17, end_day[i] == 18)))
    # Riga (index 4): days 23-24
    solver.add(Implies(order[i] == 4, And(start_day[i] == 23, end_day[i] == 24)))
    # Helsinki (index 6): overlap with 18-22
    solver.add(Implies(order[i] == 6, And(start_day[i] <= 22, end_day[i] >= 18)))

# Add flight constraints between consecutive cities
for i in range(9):
    current = order[i]
    next_c = order[i+1]
    constraints = []
    for a, b in allowed_flights:
        constraints.append(And(current == a, next_c == b))
    solver.add(Or(constraints))

# Add constraint for last end_day
solver.add(end_day[9] == 25)

# Check if solution exists
if solver.check() == sat:
    model = solver.model()
    # Extract order, start_day, end_day
    order_values = [model.evaluate(order[i]).as_long() for i in range(10)]
    start_day_values = [model.evaluate(start_day[i]).as_long() for i in range(10)]
    end_day_values = [model.evaluate(end_day[i]).as_long() for i in range(10)]
    
    # Generate itinerary
    itinerary = []
    for i in range(10):
        city_index = order_values[i]
        city_name = cities[city_index]
        start = start_day_values[i]
        end = end_day_values[i]
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city_name})
    
    # Output JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")