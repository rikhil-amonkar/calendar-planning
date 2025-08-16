from z3 import *

# Define city IDs and durations
city_ids = {
    'Rome': 0,
    'Mykonos': 1,
    'Lisbon': 2,
    'Frankfurt': 3,
    'Nice': 4,
    'Stuttgart': 5,
    'Venice': 6,
    'Dublin': 7,
    'Bucharest': 8,
    'Seville': 9
}

durations = {
    0: 3,   # Rome
    1: 2,   # Mykonos
    2: 2,   # Lisbon
    3: 5,   # Frankfurt
    4: 3,   # Nice
    5: 4,   # Stuttgart
    6: 4,   # Venice
    7: 2,   # Dublin
    8: 2,   # Bucharest
    9: 5    # Seville
}

# Define direct flights as pairs (a, b)
direct_flights_pairs = [
    (0,5), (5,0),  # Rome-Stuttgart
    (6,0), (0,6),  # Venice-Rome
    (7,8), (8,7),  # Dublin-Bucharest
    (1,0), (0,1),  # Mykonos-Rome
    (9,2), (2,9),  # Seville-Lisbon
    (3,6), (6,3),  # Frankfurt-Venice
    (6,5), (5,6),  # Venice-Stuttgart
    (8,2), (2,8),  # Bucharest-Lisbon
    (4,1), (1,4),  # Nice-Mykonos
    (6,7), (7,6),  # Venice-Dublin
    (7,2), (2,7),  # Dublin-Lisbon
    (6,4), (4,6),  # Venice-Nice
    (0,9), (9,0),  # Rome-Seville
    (3,0), (0,3),  # Frankfurt-Rome
    (4,7), (7,4),  # Nice-Dublin
    (0,7), (7,0),  # Rome-Dublin
    (0,2), (2,0),  # Rome-Lisbon
    (3,2), (2,3),  # Frankfurt-Lisbon
    (4,0), (0,4),  # Nice-Rome
    (3,4), (4,3),  # Frankfurt-Nice
    (3,5), (5,3),  # Frankfurt-Stuttgart
    (3,8), (8,3),  # Frankfurt-Bucharest
    (2,5), (5,2),  # Lisbon-Stuttgart
    (4,2), (2,4),  # Nice-Lisbon
    (9,7), (7,9)   # Seville-Dublin
]

direct_flights = set(direct_flights_pairs)

# Z3 setup
s = Solver()

# Create sequence variables
sequence = [Int('city_%d' % i) for i in range(10)]

# Add constraints: all cities are unique and between 0 and 9
for city in sequence:
    s.add(And(city >= 0, city <= 9))
s.add(Distinct(sequence))

# Add constraints for direct flights between consecutive cities
for i in range(9):
    current = sequence[i]
    next_city = sequence[i+1]
    conditions = []
    for a, b in direct_flights:
        conditions.append(And(current == a, next_city == b))
    s.add(Or(conditions))

# Create start_days variables
start_days = [Int('start_day_%d' % i) for i in range(10)]

# Add start_day[0] == 1
s.add(start_days[0] == 1)

# Define a function to get duration based on city ID
def get_duration(city_var):
    return If(city_var == 0, 3,
        If(city_var == 1, 2,
            If(city_var == 2, 2,
                If(city_var == 3, 5,
                    If(city_var == 4, 3,
                        If(city_var == 5, 4,
                            If(city_var == 6, 4,
                                If(city_var == 7, 2,
                                    If(city_var == 8, 2,
                                        If(city_var == 9, 5, 0)
                                    )
                                )
                            )
                        )
                    )
                )
            )
        )
    )

# Add constraints for start_days[i] = start_days[i-1] + duration_prev
for i in range(1, 10):
    duration_prev = get_duration(sequence[i-1])
    s.add(start_days[i] == start_days[i-1] + duration_prev)

# Add constraints for specific start_days
for i in range(10):
    # Frankfurt (3) must start on day 1
    s.add(Implies(sequence[i] == 3, start_days[i] == 1))
    # Seville (9) must start on day 13
    s.add(Implies(sequence[i] == 9, start_days[i] == 13))
    # Mykonos (1) must start on day 10
    s.add(Implies(sequence[i] == 1, start_days[i] == 10))

# Add constraint for the last city's end_day to be 23
duration_last = get_duration(sequence[9])
end_day_last = start_days[9] + duration_last - 1
s.add(end_day_last == 23)

# Check if the model is satisfiable
if s.check() == sat:
    model = s.model()
    # Extract sequence and start_days
    seq = [model.eval(sequence[i]).as_long() for i in range(10)]
    start_days_vals = [model.eval(start_days[i]).as_long() for i in range(10)]
    
    # Generate the itinerary
    itinerary_list = []
    for i in range(10):
        city_id = seq[i]
        # Get city name from ID
        city_name = [k for k, v in city_ids.items() if v == city_id][0]
        duration = durations[city_id]
        start = start_days_vals[i]
        end = start + duration - 1
        for day in range(start, end + 1):
            itinerary_list.append({'day': day, 'city': city_name})
    
    # Sort itinerary by day
    itinerary_list.sort(key=lambda x: x['day'])
    
    # Create the JSON output
    json_output = {'itinerary': itinerary_list}
    print(json.dumps(json_output, indent=2))
else:
    print("No solution found.")