from z3 import *

# Define city names and their integer mappings
cities = ['London', 'Milan', 'Zurich', 'Stockholm', 'Reykjavik', 'Stuttgart', 'Hamburg', 'Bucharest', 'Barcelona', 'Tallinn']
n = len(cities)

# Minimum durations for each city
min_dur = [3, 3, 1, 1, 4, 4, 4, 1, 3, 4]

# Define edges of the travel graph (undirected)
edges = [
    (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9),
    (1, 2), (1, 5), (1, 6), (1, 8),
    (2, 5), (2, 6),
    (3, 4), (3, 9),
    (4, 9),
    (5, 6),
    (7, 8)
]

# Create Z3 solver
s = Solver()

# Day assignment: day[d] for d in 0..27 (representing days 1 to 28)
day = [Int(f'day_{d}') for d in range(28)]
for d in range(28):
    s.add(day[d] >= 0, day[d] < 10)

# First and last day variables for each city
first_day = [Int(f'first_{i}') for i in range(10)]
last_day = [Int(f'last_{i}') for i in range(10)]

# Constraints for contiguous blocks and min duration
for i in range(10):
    # Ensure first_day and last_day are within bounds
    s.add(first_day[i] >= 0, first_day[i] < 28)
    s.add(last_day[i] >= 0, last_day[i] < 28)
    s.add(first_day[i] <= last_day[i])
    # Duration must meet minimum
    s.add(last_day[i] - first_day[i] + 1 >= min_dur[i])
    # Each city appears in its contiguous block
    for d in range(28):
        in_block = And(first_day[i] <= d, d <= last_day[i])
        s.add((day[d] == i) == in_block)

# Travel constraints for consecutive days
for d in range(27):
    same_city = day[d] == day[d+1]
    valid_transition = Or([Or(And(day[d] == a, day[d+1] == b), And(day[d] == b, day[d+1] == a)) for (a, b) in edges])
    s.add(Or(same_city, valid_transition))

# Ensure exactly 10 contiguous blocks (9 changes)
changes = [If(day[d] != day[d+1], 1, 0) for d in range(27)]
s.add(sum(changes) == 9)

# Solve the problem
if s.check() == sat:
    model = s.model()
    # Extract first_day for each city
    city_blocks = []
    for i in range(10):
        fd = model.evaluate(first_day[i]).as_long()
        ld = model.evaluate(last_day[i]).as_long()
        city_blocks.append((fd, ld, i))
    # Sort by first_day to get itinerary order
    city_blocks.sort(key=lambda x: x[0])
    itinerary = []
    for fd, ld, i in city_blocks:
        start = fd + 1  # Convert from 0-indexed to day number
        end = ld + 1
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary.append({'day_range': day_range, 'place': cities[i]})
    print(f"Plan found: {itinerary}")
else:
    print("No valid plan found.")