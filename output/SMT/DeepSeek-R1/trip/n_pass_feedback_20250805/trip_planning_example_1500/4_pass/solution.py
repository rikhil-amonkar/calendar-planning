from z3 import *

# Define city names and their integer mappings
cities = ['London', 'Milan', 'Zurich', 'Stockholm', 'Reykjavik', 'Stuttgart', 'Hamburg', 'Bucharest', 'Barcelona', 'Tallinn']
min_dur = [3, 3, 1, 1, 4, 4, 4, 1, 3, 4]  # Minimum stays for each city

# Define travel connections (undirected edges)
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

# Decision variables
city_at_pos = [Int(f'city_at_pos_{k}') for k in range(10)]  # City index at each position
starts = [Int(f'start_{k}') for k in range(10)]             # Start day for each block
durations = [Int(f'dur_{k}') for k in range(10)]            # Duration for each block
ends = [Int(f'end_{k}') for k in range(10)]                 # End day for each block

# Constraints for city assignment permutation
s.add(Distinct(city_at_pos))
for k in range(10):
    s.add(city_at_pos[k] >= 0, city_at_pos[k] < 10)

# Block sequencing constraints
s.add(starts[0] == 0)                           # Trip starts on day 0 (1 in 1-indexed)
s.add(ends[9] == 27)                            # Trip ends on day 27 (28 in 1-indexed)
for k in range(9):
    s.add(ends[k] == starts[k] + durations[k] - 1)  # Block k ends based on start+duration
    s.add(starts[k+1] == ends[k] + 1)               # Next block starts immediately after

# Duration constraints
for k in range(10):
    city_idx = city_at_pos[k]
    # Minimum stay duration
    s.add(durations[k] >= min_dur[city_idx])
    # Valid day range
    s.add(starts[k] >= 0, ends[k] < 28)

# Travel constraints between consecutive cities
for k in range(9):
    city1 = city_at_pos[k]
    city2 = city_at_pos[k+1]
    # Must have direct travel connection
    valid_edge = Or([And(city1 == a, city2 == b) for a, b in edges] + 
                  [And(city1 == b, city2 == a) for a, b in edges])
    s.add(valid_edge)

# Solve the problem
if s.check() == sat:
    model = s.model()
    itinerary = []
    for k in range(10):
        city_idx = model.evaluate(city_at_pos[k]).as_long()
        start_day = model.evaluate(starts[k]).as_long() + 1  # Convert to 1-indexed
        end_day = model.evaluate(ends[k]).as_long() + 1      # Convert to 1-indexed
        
        # Format day range string
        if start_day == end_day:
            day_range = f"Day {start_day}"
        else:
            day_range = f"Day {start_day}-{end_day}"
        
        itinerary.append({'day_range': day_range, 'place': cities[city_idx]})
    
    print(f"Plan found: {{'itinerary': {itinerary}}}")
else:
    print("No valid plan found.")