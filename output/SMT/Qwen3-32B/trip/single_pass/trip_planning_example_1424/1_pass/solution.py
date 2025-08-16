import z3

# Define cities and their durations
city_list = ['Porto', 'Amsterdam', 'Helsinki', 'Reykjavik', 'Warsaw', 'Naples', 'Brussels', 'Valencia', 'Lyon', 'Split']
durations = [5, 4, 4, 5, 3, 4, 3, 2, 3, 3]

# Define direct flights
direct_flights_given = [
    ('Amsterdam', 'Warsaw'),
    ('Helsinki', 'Brussels'),
    ('Helsinki', 'Warsaw'),
    ('Reykjavik', 'Brussels'),
    ('Amsterdam', 'Lyon'),
    ('Amsterdam', 'Naples'),
    ('Amsterdam', 'Reykjavik'),
    ('Naples', 'Valencia'),
    ('Porto', 'Brussels'),
    ('Amsterdam', 'Split'),
    ('Lyon', 'Split'),
    ('Warsaw', 'Split'),
    ('Porto', 'Amsterdam'),
    ('Helsinki', 'Split'),
    ('Brussels', 'Lyon'),
    ('Porto', 'Lyon'),
    ('Reykjavik', 'Warsaw'),
    ('Brussels', 'Valencia'),
    ('Valencia', 'Lyon'),
    ('Porto', 'Valencia'),
    ('Warsaw', 'Brussels'),
    ('Warsaw', 'Naples'),
    ('Naples', 'Split'),
    ('Helsinki', 'Naples'),
    ('Helsinki', 'Reykjavik'),
    ('Amsterdam', 'Valencia'),
    ('Naples', 'Brussels'),
]

direct_flights = set()
for a, b in direct_flights_given:
    direct_flights.add((a, b))
    direct_flights.add((b, a))

# Create flight matrix
flight_matrix = [[False for _ in range(10)] for _ in range(10)]
for i in range(10):
    for j in range(10):
        if (city_list[i], city_list[j]) in direct_flights:
            flight_matrix[i][j] = True

s = z3.Solver()

# Define sequence variables
seq = [z3.Int(f'seq_{i}') for i in range(10)]

# Constraints: all distinct and between 0 and 9
s.add([z3.And(0 <= seq[i], seq[i] <= 9) for i in range(10)])
s.add(z3.Distinct(seq))

# Define start_days variables
start_days = [z3.Int(f's_{i}') for i in range(10)]

# start_days[0] = 1
s.add(start_days[0] == 1)

# For i >= 1, start_days[i] = start_days[i-1] + duration of previous city - 1
for i in range(1, 10):
    prev_duration = z3.If(seq[i-1] == 0, 5,
        z3.If(seq[i-1] == 1, 4,
            z3.If(seq[i-1] == 2, 4,
                z3.If(seq[i-1] == 3, 5,
                    z3.If(seq[i-1] == 4, 3,
                        z3.If(seq[i-1] == 5, 4,
                            z3.If(seq[i-1] == 6, 3,
                                z3.If(seq[i-1] == 7, 2,
                                    z3.If(seq[i-1] == 8, 3, 3)
                                )
                            )
                        )
                    )
                )
            )
        )
    )
    s.add(start_days[i] == start_days[i-1] + prev_duration - 1)

# Add constraints for fixed start_days
fixed_start = {
    'Porto': 1,
    'Amsterdam': 5,
    'Helsinki': 8,
    'Naples': 17,
    'Brussels': 20,
}

city_to_index = {city: i for i, city in enumerate(city_list)}
for city, required in fixed_start.items():
    index = city_to_index[city]
    for i in range(10):
        s.add(z3.Implies(seq[i] == index, start_days[i] == required))

# Add flight constraints for consecutive cities
for i in range(9):
    constraints = []
    for a in range(10):
        for b in range(10):
            if flight_matrix[a][b]:
                constraints.append(z3.And(seq[i] == a, seq[i+1] == b))
    s.add(z3.Or(*constraints))

# Check if the solver can find a solution
if s.check() == z3.sat:
    model = s.model()
    # Extract the sequence
    sequence = [model.evaluate(seq[i]).as_long() for i in range(10)]
    # Extract start_days
    start_days_values = [model.evaluate(start_days[i]).as_long() for i in range(10)]
    # Build the itinerary
    itinerary = []
    for day in range(1, 28):  # 27 days
        for i in range(10):
            city_index = sequence[i]
            start = start_days_values[i]
            duration = durations[city_index]
            end = start + duration - 1
            if start <= day <= end:
                itinerary.append({
                    'day': day,
                    'city': city_list[city_index]
                })
                break
    # Now, format the itinerary as a list of day-place mappings sorted by day
    itinerary.sort(key=lambda x: x['day'])
    # Convert to the required JSON format
    json_output = {'itinerary': [{'day': item['day'], 'place': item['city']} for item in itinerary]}
    print(json_output)
else:
    print("No solution found.")