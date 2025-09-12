from z3 import *
import json

# Define the cities and their required days and must_include_days
cities = ['London', 'Milan', 'Reykjavik', 'Zurich', 'Bucharest', 'Hamburg', 'Barcelona', 'Stuttgart', 'Stockholm', 'Tallinn']
required_days = {
    'London': 3,
    'Milan': 5,
    'Reykjavik': 5,
    'Zurich': 2,
    'Bucharest': 2,
    'Hamburg': 5,
    'Barcelona': 4,
    'Stuttgart': 5,
    'Stockholm': 2,
    'Tallinn': 4,
}
must_include_days = {
    'London': [(1, 3)],
    'Milan': [(3, 7)],
    'Reykjavik': [(9, 13)],
    'Zurich': [(7, 8)],
    'Bucharest': [],
    'Hamburg': [],
    'Barcelona': [],
    'Stuttgart': [],
    'Stockholm': [],
    'Tallinn': [],
}

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

# Create variables for the sequence of cities (permutation)
sequence = [Int(f'seq_{i}') for i in range(10)]

# Map each city to an index
city_to_index = {city: i for i, city in enumerate(cities)}

# Add constraints that each position in the sequence is a valid city index
for i in range(10):
    s.add(And(sequence[i] >= 0, sequence[i] < 10))

# Add constraint that all cities in the sequence are distinct (permutation)
s.add(Distinct(sequence))

# Define duration, start, and end for each city in the sequence
duration = [Int(f'duration_{i}') for i in range(10)]
start = [Int(f'start_{i}') for i in range(10)]
end = [Int(f'end_{i}') for i in range(10)]

# First day is day 1
s.add(start[0] == 1)

# Start of next city is end of previous city
for i in range(1, 10):
    s.add(start[i] == end[i-1])

# End is start + duration - 1
for i in range(10):
    s.add(end[i] == start[i] + duration[i] - 1)

# Total duration is 28
s.add(Sum(duration) == 28)

# Apply duration constraints and must_include_days
for i in range(10):
    city_idx = sequence[i]
    city_name = If(
        city_idx == 0, 'London',
        If(city_idx == 1, 'Milan',
           If(city_idx == 2, 'Reykjavik',
              If(city_idx == 3, 'Zurich',
                 If(city_idx == 4, 'Bucharest',
                    If(city_idx == 5, 'Hamburg',
                       If(city_idx == 6, 'Barcelona',
                          If(city_idx == 7, 'Stuttgart',
                             If(city_idx == 8, 'Stockholm', 'Tallinn')))))))))
    required = required_days[city_name]
    s.add(duration[i] >= required)

    for (day_start, day_end) in must_include_days[city_name]:
        s.add(And(start[i] <= day_start, end[i] >= day_end))

# Flight matrix for direct flights
flight_matrix = [[False] * 10 for _ in range(10)]
for (a, b) in direct_flights:
    a_idx = cities.index(a)
    b_idx = cities.index(b)
    flight_matrix[a_idx][b_idx] = True

# Add flight constraints between consecutive cities
for i in range(9):
    current_city_idx = sequence[i]
    next_city_idx = sequence[i+1]
    valid_transitions = []
    for a in range(10):
        for b in range(10):
            if flight_matrix[a][b]:
                valid_transitions.append(And(current_city_idx == a, next_city_idx == b))
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