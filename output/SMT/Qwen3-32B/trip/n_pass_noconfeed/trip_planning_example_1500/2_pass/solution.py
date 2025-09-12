from z3 import *
import json

# Define cities and their index-based data
cities = ['London', 'Milan', 'Reykjavik', 'Zurich', 'Bucharest', 'Hamburg', 'Barcelona', 'Stuttgart', 'Stockholm', 'Tallinn']

# City-specific data by index
required_days_by_index = [3, 5, 5, 2, 2, 5, 4, 5, 2, 4]
must_include_days_by_index = [
    [(1, 3)],  # London
    [(3, 7)],  # Milan
    [(9, 13)],  # Reykjavik
    [(7, 8)],  # Zurich
    [],  # Bucharest
    [],  # Hamburg
    [],  # Barcelona
    [],  # Stuttgart
    [],  # Stockholm
    [],  # Tallinn
]

# Direct flights between cities
direct_flights = {
    ('London', 'Hamburg'), ('Hamburg', 'London'),
    ('London', 'Reykjavik'), ('Reykjavik', 'London'),
    ('Milan', 'Barcelona'), ('Barcelona', 'Milan'),
    ('Reykjavik', 'Barcelona'), ('Barcelona', 'Reykjavik'),
    ('Reykjavik', 'Stuttgart'), ('Stuttgart', 'Reykjavik'),
    ('Stockholm', 'Reykjavik'), ('Reykjavik', 'Stockholm'),
    ('London', 'Stuttgart'), ('Stuttgart', 'London'),
    ('Milan', 'Zurich'), ('Zurich', 'Milan'),
    ('London', 'Barcelona'), ('Barcelona', 'London'),
    ('Stockholm', 'Hamburg'), ('Hamburg', 'Stockholm'),
    ('Zurich', 'Barcelona'), ('Barcelona', 'Zurich'),
    ('Stockholm', 'Stuttgart'), ('Stuttgart', 'Stockholm'),
    ('Milan', 'Hamburg'), ('Hamburg', 'Milan'),
    ('Stockholm', 'Tallinn'), ('Tallinn', 'Stockholm'),
    ('Hamburg', 'Bucharest'), ('Bucharest', 'Hamburg'),
    ('London', 'Bucharest'), ('Bucharest', 'London'),
    ('Milan', 'Stockholm'), ('Stockholm', 'Milan'),
    ('Milan', 'Stuttgart'), ('Stuttgart', 'Milan'),
    ('Stockholm', 'Barcelona'), ('Barcelona', 'Stockholm'),
    ('London', 'Milan'), ('Milan', 'London'),
    ('Zurich', 'Hamburg'), ('Hamburg', 'Zurich'),
    ('Bucharest', 'Barcelona'), ('Barcelona', 'Bucharest'),
    ('Zurich', 'Stockholm'), ('Stockholm', 'Zurich'),
    ('Barcelona', 'Tallinn'), ('Tallinn', 'Barcelona'),
    ('Zurich', 'Tallinn'), ('Tallinn', 'Zurich'),
    ('Hamburg', 'Barcelona'), ('Barcelona', 'Hamburg'),
    ('Stuttgart', 'Barcelona'), ('Barcelona', 'Stuttgart'),
    ('Zurich', 'Reykjavik'), ('Reykjavik', 'Zurich'),
    ('Zurich', 'Bucharest'), ('Bucharest', 'Zurich'),
}

# Create a solver
s = Solver()

# Sequence of cities (permutation)
sequence = [Int(f'seq_{i}') for i in range(10)]

# Add constraints for valid city indices and distinct sequence
for i in range(10):
    s.add(And(sequence[i] >= 0, sequence[i] < 10))
s.add(Distinct(sequence))

# Duration, start, and end for each city in sequence
duration = [Int(f'duration_{i}') for i in range(10)]
start = [Int(f'start_{i}') for i in range(10)]
end = [Int(f'end_{i}') for i in range(10)]

# First day is day 1
s.add(start[0] == 1)

# Start of next city is end of previous
for i in range(1, 10):
    s.add(start[i] == end[i - 1])

# End is start + duration - 1
for i in range(10):
    s.add(end[i] == start[i] + duration[i] - 1)

# Total duration is 28
s.add(Sum(duration) == 28)

# Apply duration and must_include constraints using Z3 If expressions
for i in range(10):
    city_idx = sequence[i]
    # Build required days expression
    required_expr = If(city_idx == 0, required_days_by_index[0],
                       If(city_idx == 1, required_days_by_index[1],
                          If(city_idx == 2, required_days_by_index[2],
                             If(city_idx == 3, required_days_by_index[3],
                                If(city_idx == 4, required_days_by_index[4],
                                   If(city_idx == 5, required_days_by_index[5],
                                      If(city_idx == 6, required_days_by_index[6],
                                         If(city_idx == 7, required_days_by_index[7],
                                            If(city_idx == 8, required_days_by_index[8],
                                               required_days_by_index[9]))))))))
    s.add(duration[i] >= required_expr)

    # Add must_include constraints
    for j in range(10):
        for (s_day, e_day) in must_include_days_by_index[j]:
            s.add(Implies(city_idx == j, And(start[i] <= s_day, end[i] >= e_day)))

# Flight constraints between consecutive cities
for i in range(9):
    current_city = sequence[i]
    next_city = sequence[i + 1]
    valid_transitions = []
    for a in range(10):
        for b in range(10):
            if (cities[a], cities[b]) in direct_flights:
                valid_transitions.append(And(current_city == a, next_city == b))
    s.add(Or(valid_transitions))

# Check for solution and output
if s.check() == sat:
    m = s.model()
    seq_values = [m.eval(sequence[i]).as_long() for i in range(10)]
    cities_order = [cities[idx] for idx in seq_values]
    durations = [m.eval(duration[i]).as_long() for i in range(10)]
    starts = [m.eval(start[i]).as_long() for i in range(10)]
    ends = [m.eval(end[i]).as_long() for i in range(10)]
    itinerary = []
    for i in range(10):
        city = cities_order[i]
        start_day = starts[i]
        end_day = ends[i]
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))