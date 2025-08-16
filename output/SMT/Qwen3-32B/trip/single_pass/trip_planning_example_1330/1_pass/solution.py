from z3 import *

# Define cities and their durations
cities = ['Salzburg', 'Venice', 'Bucharest', 'Brussels', 'Hamburg', 'Copenhagen', 'Nice', 'Zurich', 'Naples']
durations = {
    'Salzburg': 2,
    'Venice': 5,
    'Bucharest': 4,
    'Brussels': 2,
    'Hamburg': 4,
    'Copenhagen': 4,
    'Nice': 3,
    'Zurich': 5,
    'Naples': 4
}

# Define direct flights
direct_flights = set()
flights_list = [
    ('Zurich', 'Brussels'),
    ('Bucharest', 'Copenhagen'),
    ('Venice', 'Brussels'),
    ('Nice', 'Zurich'),
    ('Hamburg', 'Nice'),
    ('Zurich', 'Naples'),
    ('Hamburg', 'Bucharest'),
    ('Zurich', 'Copenhagen'),
    ('Bucharest', 'Brussels'),
    ('Hamburg', 'Brussels'),
    ('Venice', 'Brussels'),
    ('Venice', 'Naples'),
    ('Venice', 'Copenhagen'),
    ('Bucharest', 'Naples'),
    ('Hamburg', 'Copenhagen'),
    ('Venice', 'Zurich'),
    ('Nice', 'Brussels'),
    ('Hamburg', 'Venice'),
    ('Copenhagen', 'Naples'),
    ('Nice', 'Naples'),
    ('Hamburg', 'Zurich'),
    ('Salzburg', 'Hamburg'),
    ('Zurich', 'Bucharest'),
    ('Brussels', 'Naples'),
    ('Copenhagen', 'Brussels'),
    ('Venice', 'Nice'),
    ('Nice', 'Copenhagen'),
]
for a, b in flights_list:
    direct_flights.add((a, b))
    direct_flights.add((b, a))

# Create city index mapping
city_to_index = {city: i for i, city in enumerate(cities)}

# Build direct flight matrix
direct_flight_matrix = [[False for _ in range(9)] for _ in range(9)]
for a, b in direct_flights:
    a_idx = city_to_index[a]
    b_idx = city_to_index[b]
    direct_flight_matrix[a_idx][b_idx] = True

# Z3 setup
solver = Solver()

# Variables for permutation (positions)
positions = [Int(f'pos_{i}') for i in range(9)]

# Constraints for permutation: each is between 0 and 8, all distinct
for i in range(9):
    solver.add(And(0 <= positions[i], positions[i] < 9))
solver.add(Distinct(positions))

# Variables for start days
start_days = [Int(f'start_day_{i}') for i in range(9)]

# First start day is 1
solver.add(start_days[0] == 1)

# Define durations_z3
durations_z3 = [IntVal(durations[city]) for city in cities]

# Function to get duration based on index
def get_duration(index_var):
    expr = IntVal(0)
    for i in range(9):
        expr = If(index_var == i, durations_z3[i], expr)
    return expr

# Constraints for start_days based on previous durations
for i in range(1, 9):
    prev_duration = get_duration(positions[i-1])
    solver.add(start_days[i] == start_days[i-1] + prev_duration)

# Constraints for specific start days
for i in range(9):
    # Nice (index 6) must start on day 9
    solver.add(If(positions[i] == 6, start_days[i] == 9, True))
    # Copenhagen (index 5) must start on day 18
    solver.add(If(positions[i] == 5, start_days[i] == 18, True))
    # Brussels (index 3) must start on day 21
    solver.add(If(positions[i] == 3, start_days[i] == 21, True))
    # Naples (index 8) must start on day 22
    solver.add(If(positions[i] == 8, start_days[i] == 22, True))

# Constraint for last day
last_duration = get_duration(positions[8])
end_day_last = start_days[8] + last_duration - 1
solver.add(end_day_last == 25)

# Constraints for direct flights between consecutive cities
for i in range(8):
    current_city_idx = positions[i]
    next_city_idx = positions[i+1]
    expr = False
    for a in range(9):
        for b in range(9):
            if direct_flight_matrix[a][b]:
                expr = Or(expr, And(current_city_idx == a, next_city_idx == b))
    solver.add(expr)

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    # Extract positions and start_days
    positions_values = [model.eval(p).as_long() for p in positions]
    start_days_values = [model.eval(sd).as_long() for sd in start_days]
    
    # Build the itinerary
    itinerary = {}
    for i in range(9):
        city_idx = positions_values[i]
        city_name = cities[city_idx]
        start_day = start_days_values[i]
        duration = durations[city_name]
        for day in range(start_day, start_day + duration):
            itinerary[day] = city_name
    
    # Sort the itinerary by day
    sorted_days = sorted(itinerary.keys())
    result = {'itinerary': [{'day': day, 'city': itinerary[day]} for day in sorted_days]]
    
    # Print the JSON-formatted result
    import json
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")