from z3 import *
import json

# Define cities and their durations
cities = ["Venice", "Barcelona", "Copenhagen", "Lyon", "Reykjavik", "Dubrovnik", "Athens", "Tallinn", "Munich"]
durations_list = [4, 3, 4, 4, 4, 5, 2, 5, 3]

# Generate allowed_pairs based on direct flights
direct_flights = [
    (2,6), (2,5), (8,7), (2,8), (0,8), (4,6), (6,5), (0,6), (3,1), (2,4), (4,8), (6,8), (3,8), (1,4), (0,5), (1,5), (3,0), (5,8), (1,6), (2,1), (0,1), (1,8), (1,7), (2,7)
]
allowed_pairs = set()
for a, b in direct_flights:
    allowed_pairs.add((a, b))
    allowed_pairs.add((b, a))

# Initialize Z3 solver
solver = Solver()

# Create sequence variables for the 9 cities
sequence = [Int(f'city_{i}') for i in range(9)]

# Add constraints: all distinct and within range
solver.add(Distinct(sequence))
for city in sequence:
    solver.add(And(0 <= city, city <= 8))

# Define a function to get the duration of a city by its index
duration_func = Function('duration_func', IntSort(), IntSort())

# Add constraints for the duration function
for city_idx in range(9):
    solver.add(duration_func(city_idx) == durations_list[city_idx])

# Create start_days variables
start_days = [Int(f'start_day_{i}') for i in range(9)]

# Add constraints for start_days
solver.add(start_days[0] == 1)

for i in range(1, 9):
    duration_prev = duration_func(sequence[i-1])
    solver.add(start_days[i] == start_days[i-1] + duration_prev - 1)

# The end day of the last city must be 26
last_duration = duration_func(sequence[8])
solver.add(start_days[8] + last_duration - 1 == 26)

# Add constraints for direct flights between consecutive cities
for i in range(8):
    a = sequence[i]
    b = sequence[i+1]
    constraints = []
    for (allowed_a, allowed_b) in allowed_pairs:
        constraints.append(And(a == allowed_a, b == allowed_b))
    solver.add(Or(constraints))

# Add constraints for specific event days
for i in range(9):
    # Barcelona (index 1): start_day between 8 and 12 inclusive
    solver.add(Implies(sequence[i] == 1, And(start_days[i] >= 8, start_days[i] <= 12)))
    # Copenhagen (index 2): start_day between 4 and 10 inclusive
    solver.add(Implies(sequence[i] == 2, And(start_days[i] >= 4, start_days[i] <= 10)))
    # Dubrovnik (index 5): start_day between 12 and 20 inclusive
    solver.add(Implies(sequence[i] == 5, And(start_days[i] >= 12, start_days[i] <= 20)))

# Check for a solution
if solver.check() == sat:
    model = solver.model()
    # Extract the sequence of cities and start days
    sequence_values = [model.evaluate(city).as_long() for city in sequence]
    start_days_values = [model.evaluate(start_days[i]).as_long() for i in range(9)]
    
    # Build the itinerary
    itinerary = {}
    for i in range(9):
        city_idx = sequence_values[i]
        city_name = cities[city_idx]
        start = start_days_values[i]
        duration = durations_list[city_idx]
        end = start + duration - 1
        for day in range(start, end + 1):
            itinerary[day] = city_name
    
    # Format the result as JSON
    result = {'itinerary': [{'day': day, 'city': city} for day, city in sorted(itinerary.items())]}
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")