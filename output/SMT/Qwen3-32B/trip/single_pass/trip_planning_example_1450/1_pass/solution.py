from z3 import *
import json

# Define cities and their durations
cities = ['Stockholm', 'Hamburg', 'Florence', 'Istanbul', 'Oslo', 'Vilnius', 'Santorini', 'Munich', 'Frankfurt', 'Krakow']
durations = [3, 5, 2, 5, 5, 5, 2, 5, 4, 5]

# Create Z3 solver
s = Solver()

# Sequence variables for the 10 cities (each is an index from 0 to 9)
seq = [Int(f'seq_{i}') for i in range(10)]

# All sequence variables must be between 0 and 9
for i in range(10):
    s.add(And(seq[i] >= 0, seq[i] <= 9))

# All cities must be visited exactly once
s.add(Distinct(seq))

# Start and end day variables for each position in the sequence
start_day = [Int(f'start_{i}') for i in range(10)]
end_day = [Int(f'end_{i}') for i in range(10)]

# Define start_day and end_day for each position
for i in range(10):
    # Compute duration for the city at this position
    duration_i = If(seq[i] == 0, 3,
               If(seq[i] == 1, 5,
               If(seq[i] == 2, 2,
               If(seq[i] == 3, 5,
               If(seq[i] == 4, 5,
               If(seq[i] == 5, 5,
               If(seq[i] == 6, 2,
               If(seq[i] == 7, 5,
               If(seq[i] == 8, 4,
               If(seq[i] == 9, 5, 0))))))))))
    
    # Compute start_day[i]
    if i == 0:
        start_expr = If(seq[i] == 9, 5, If(seq[i] == 3, 25, 1))
    else:
        start_expr = If(seq[i] == 9, 5, If(seq[i] == 3, 25, end_day[i-1]))
    s.add(start_day[i] == start_expr)
    
    # end_day[i] = start_day[i] + duration_i - 1
    s.add(end_day[i] == start_day[i] + duration_i - 1)

# Constraint: end_day of last city must be 32
s.add(end_day[9] == 32)

# Define allowed direct flights as pairs of city indices
allowed_flights = set()
allowed_flights.add((4, 0))  # Oslo-Stockholm
allowed_flights.add((0, 4))
allowed_flights.add((9, 8))  # Krakow-Frankfurt
allowed_flights.add((8, 9))
allowed_flights.add((9, 3))  # Krakow-Istanbul
allowed_flights.add((3, 9))
allowed_flights.add((7, 0))  # Munich-Stockholm
allowed_flights.add((0, 7))
allowed_flights.add((1, 0))  # Hamburg-Stockholm
allowed_flights.add((0, 1))
allowed_flights.add((9, 5))  # Krakow-Vilnius
allowed_flights.add((5, 9))
allowed_flights.add((4, 3))  # Oslo-Istanbul
allowed_flights.add((3, 4))
allowed_flights.add((3, 0))  # Istanbul-Stockholm
allowed_flights.add((0, 3))
allowed_flights.add((4, 9))  # Oslo-Krakow
allowed_flights.add((9, 4))
allowed_flights.add((5, 3))  # Vilnius-Istanbul
allowed_flights.add((3, 5))
allowed_flights.add((4, 5))  # Oslo-Vilnius
allowed_flights.add((5, 4))
allowed_flights.add((8, 3))  # Frankfurt-Istanbul
allowed_flights.add((3, 8))
allowed_flights.add((4, 8))  # Oslo-Frankfurt
allowed_flights.add((8, 4))
allowed_flights.add((7, 1))  # Munich-Hamburg
allowed_flights.add((1, 7))
allowed_flights.add((7, 3))  # Munich-Istanbul
allowed_flights.add((3, 7))
allowed_flights.add((4, 7))  # Oslo-Munich
allowed_flights.add((7, 4))
allowed_flights.add((8, 2))  # Frankfurt-Florence
allowed_flights.add((2, 8))
allowed_flights.add((4, 1))  # Oslo-Hamburg
allowed_flights.add((1, 4))
allowed_flights.add((5, 8))  # Vilnius-Frankfurt
allowed_flights.add((8, 5))
allowed_flights.add((2, 7))  # Florence-Munich
allowed_flights.add((7, 2))
allowed_flights.add((9, 7))  # Krakow-Munich
allowed_flights.add((7, 9))
allowed_flights.add((1, 3))  # Hamburg-Istanbul
allowed_flights.add((3, 1))
allowed_flights.add((8, 0))  # Frankfurt-Stockholm
allowed_flights.add((0, 8))
allowed_flights.add((0, 6))  # Stockholm-Santorini
allowed_flights.add((6, 0))
allowed_flights.add((6, 4))  # Santorini-Oslo
allowed_flights.add((4, 6))
allowed_flights.add((5, 7))  # Vilnius-Munich
allowed_flights.add((7, 5))

# Add constraints for direct flights between consecutive cities
for i in range(9):
    constraints = []
    for a, b in allowed_flights:
        constraints.append(And(seq[i] == a, seq[i+1] == b))
    s.add(Or(constraints))

# Solve the constraints
if s.check() == sat:
    model = s.model()
    # Extract the sequence
    sequence = [model.evaluate(seq[i]).as_long() for i in range(10)]
    # Extract start and end days
    start_days = [model.evaluate(start_day[i]).as_long() for i in range(10)]
    end_days = [model.evaluate(end_day[i]).as_long() for i in range(10)]
    
    # Build the itinerary
    itinerary = []
    for i in range(10):
        city_index = sequence[i]
        city_name = cities[city_index]
        s_day = start_days[i]
        e_day = end_days[i]
        for day in range(s_day, e_day + 1):
            itinerary.append({"day": day, "city": city_name})
    
    # Output the JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")