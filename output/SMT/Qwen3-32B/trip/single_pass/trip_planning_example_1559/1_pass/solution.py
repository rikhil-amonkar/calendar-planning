from z3 import *

# Define cities and their durations
cities = ['Valencia', 'Oslo', 'Lyon', 'Prague', 'Paris', 'Nice', 'Seville', 'Tallinn', 'Mykonos', 'Lisbon']
durations = [2, 3, 4, 3, 4, 4, 5, 2, 5, 2]

# Define allowed flights as pairs of city indices
allowed_flights = set([
    (9, 4), (4, 9), (2, 5), (5, 2), (7, 1), (1, 7),
    (3, 2), (2, 3), (4, 1), (1, 4), (9, 6), (6, 9),
    (3, 9), (9, 3), (1, 5), (5, 1), (0, 4), (4, 0),
    (0, 9), (9, 0), (4, 5), (5, 4), (5, 8), (8, 5),
    (4, 2), (2, 4), (0, 2), (2, 0), (3, 1), (1, 3),
    (3, 4), (4, 3), (6, 4), (4, 6), (1, 2), (2, 1),
    (3, 0), (0, 3), (9, 5), (5, 9), (9, 1), (1, 9),
    (0, 6), (6, 0), (9, 2), (2, 9), (4, 7), (7, 4),
    (3, 7), (7, 3)
])

# Create Z3 variables for the sequence of cities
sequence = [Int(f'sequence_{i}') for i in range(10)]
s = Solver()

# Ensure each city is visited exactly once
for i in range(10):
    s.add(And(0 <= sequence[i], sequence[i] < 10))
s.add(Distinct(sequence))

# Calculate start_day for each position in the sequence
start_day = [Int(f'start_day_{i}') for i in range(10)]
s.add(start_day[0] == 1)
for i in range(1, 10):
    s.add(start_day[i] == start_day[i-1] + durations[sequence[i-1]])

# Constraints for specific cities
for i in range(10):
    # Seville must start on day 5
    s.add(If(sequence[i] == 6, start_day[i] == 5, True))
    # Mykonos must start on day 21
    s.add(If(sequence[i] == 8, start_day[i] == 21, True))
    # Valencia must start on day 2, 3, or 4
    s.add(If(sequence[i] == 0, And(2 <= start_day[i], start_day[i] <= 4), True))
    # Oslo must start on day 11-15
    s.add(If(sequence[i] == 1, And(11 <= start_day[i], start_day[i] <= 15), True))

# Ensure transitions between cities are direct flights
allowed_pairs = list(allowed_flights)
for i in range(9):
    current = sequence[i]
    next_c = sequence[i+1]
    constraints = []
    for a, b in allowed_pairs:
        constraints.append(And(current == a, next_c == b))
    s.add(Or(constraints))

# Check for a solution
if s.check() == sat:
    model = s.model()
    seq_values = [model.eval(sequence[i]).as_long() for i in range(10)]
    start_day_values = [model.eval(start_day[i]).as_long() for i in range(10)]
    
    # Build the itinerary
    itinerary = []
    for i in range(10):
        city_idx = seq_values[i]
        city_name = cities[city_idx]
        duration = durations[city_idx]
        start = start_day_values[i]
        end = start + duration - 1
        for day in range(start, end + 1):
            itinerary.append({day: city_name})
    
    # Sort itinerary by day
    sorted_itinerary = sorted(itinerary, key=lambda x: list(x.keys())[0])
    
    # Convert to JSON format
    result = {"itinerary": sorted_itinerary}
    print(result)
else:
    print("No solution found.")