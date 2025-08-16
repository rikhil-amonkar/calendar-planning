import z3
import json

# Define cities and their durations
cities = ['Copenhagen', 'Geneva', 'Mykonos', 'Naples', 'Prague', 'Dubrovnik', 'Athens', 'Santorini', 'Brussels', 'Munich']
durations = [5, 3, 2, 4, 2, 3, 4, 5, 4, 5]  # Duration for each city index

# Direct flights between cities (converted to city indices later)
direct_flights = [
    ('Copenhagen', 'Dubrovnik'),
    ('Brussels', 'Copenhagen'),
    ('Prague', 'Geneva'),
    ('Athens', 'Geneva'),
    ('Naples', 'Dubrovnik'),
    ('Athens', 'Dubrovnik'),
    ('Geneva', 'Mykonos'),
    ('Naples', 'Mykonos'),
    ('Naples', 'Copenhagen'),
    ('Munich', 'Mykonos'),
    ('Naples', 'Athens'),
    ('Prague', 'Athens'),
    ('Santorini', 'Geneva'),
    ('Athens', 'Santorini'),
    ('Naples', 'Munich'),
    ('Prague', 'Copenhagen'),
    ('Brussels', 'Naples'),
    ('Athens', 'Copenhagen'),
    ('Naples', 'Geneva'),
    ('Dubrovnik', 'Munich'),
    ('Brussels', 'Munich'),
    ('Prague', 'Brussels'),
    ('Brussels', 'Athens'),
    ('Athens', 'Munich'),
    ('Geneva', 'Munich'),
    ('Copenhagen', 'Munich'),
    ('Brussels', 'Geneva'),
    ('Copenhagen', 'Geneva'),
    ('Prague', 'Munich'),
    ('Copenhagen', 'Santorini'),
    ('Naples', 'Santorini'),
    ('Geneva', 'Dubrovnik'),
]

# Convert direct flights to city index pairs
allowed_pairs = set()
for (city1, city2) in direct_flights:
    idx1 = cities.index(city1)
    idx2 = cities.index(city2)
    allowed_pairs.add((idx1, idx2))
    allowed_pairs.add((idx2, idx1))

# Z3 solver
s = z3.Solver()

# Order variables (permutation of cities)
order = [z3.Int(f'order_{i}') for i in range(10)]

# Constraints: all order variables are distinct and between 0 and 9
for var in order:
    s.add(z3.And(0 <= var, var <= 9))
s.add(z3.Distinct(order))

# Position variables for cities with constraints
pos_myo = z3.Int('pos_myo')  # Mykonos (index 2)
pos_cph = z3.Int('pos_cph')  # Copenhagen (index 0)
pos_nap = z3.Int('pos_nap')  # Naples (index 3)
pos_ath = z3.Int('pos_ath')  # Athens (index 6)

# Constraints for position variables
for j in range(10):
    s.add(z3.Or(z3.And(order[j] == 2, pos_myo == j)))
    s.add(z3.Or(z3.And(order[j] == 0, pos_cph == j)))
    s.add(z3.Or(z3.And(order[j] == 3, pos_nap == j)))
    s.add(z3.Or(z3.And(order[j] == 6, pos_ath == j)))

# Start and end day variables
start_days = [z3.Int(f'start_{i}') for i in range(10)]
end_days = [z3.Int(f'end_{i}') for i in range(10)]

# Function to get duration based on city index
def get_duration(city_idx_var):
    return z3.If(city_idx_var == 0, 5,
        z3.If(city_idx_var == 1, 3,
        z3.If(city_idx_var == 2, 2,
        z3.If(city_idx_var == 3, 4,
        z3.If(city_idx_var == 4, 2,
        z3.If(city_idx_var == 5, 3,
        z3.If(city_idx_var == 6, 4,
        z3.If(city_idx_var == 7, 5,
        z3.If(city_idx_var == 8, 4,
        z3.If(city_idx_var == 9, 5, 0)))))))))

# Add constraints for start_days and end_days
s.add(start_days[0] == 1)
s.add(end_days[0] == start_days[0] + get_duration(order[0]) - 1)

for i in range(1, 10):
    s.add(start_days[i] == end_days[i-1])
    duration_i = get_duration(order[i])
    s.add(end_days[i] == start_days[i] + duration_i - 1)

# Add constraints for specific cities
s.add(start_days[pos_myo] == 27)
s.add(end_days[pos_myo] == 28)
s.add(z3.And(start_days[pos_cph] <= 15, end_days[pos_cph] >= 11))
s.add(z3.And(start_days[pos_nap] <= 8, end_days[pos_nap] >= 5))
s.add(z3.And(start_days[pos_ath] <= 11, end_days[pos_ath] >= 8))

# Add flight constraints between consecutive cities
for i in range(9):
    current = order[i]
    next_c = order[i+1]
    allowed = []
    for (a, b) in allowed_pairs:
        allowed.append(z3.And(current == a, next_c == b))
    s.add(z3.Or(allowed))

# Solve and output itinerary
if s.check() == z3.sat:
    model = s.model()
    order_list = [model.eval(order[i]).as_long() for i in range(10)]
    start = 1
    itinerary = []
    for city_idx in order_list:
        duration = durations[city_idx]
        end = start + duration - 1
        for day in range(start, end + 1):
            itinerary.append({'day': day, 'city': cities[city_idx]})
        start = end
    print(json.dumps({'itinerary': itinerary}, indent=2))
else:
    print("No solution found.")