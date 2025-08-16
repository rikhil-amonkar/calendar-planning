from z3 import *
import json

# Define cities and their durations
cities = ['Brussels', 'Rome', 'Dubrovnik', 'Geneva', 'Budapest', 'Riga', 'Valencia']
durations = {
    'Brussels': 5,
    'Rome': 2,
    'Dubrovnik': 3,
    'Geneva': 5,
    'Budapest': 2,
    'Riga': 4,
    'Valencia': 2
}

# Allowed flights: from city to list of cities
allowed_flights = {
    'Brussels': ['Valencia', 'Rome', 'Geneva', 'Riga', 'Budapest'],
    'Rome': ['Valencia', 'Geneva', 'Riga', 'Budapest', 'Brussels'],
    'Dubrovnik': ['Geneva', 'Rome'],
    'Geneva': ['Brussels', 'Rome', 'Dubrovnik', 'Valencia', 'Budapest'],
    'Budapest': ['Geneva', 'Riga', 'Rome', 'Brussels'],
    'Riga': ['Brussels', 'Rome'],
    'Valencia': ['Brussels', 'Rome', 'Geneva']
}

# Map city names to indices for easier handling
city_to_idx = {city: idx for idx, city in enumerate(cities)}

# Create Z3 solver
s = Solver()

# Sequence of cities: 7 variables, each representing a city index (0-6)
seq = [Int(f'seq_{i}') for i in range(7)]

# Start days for each city in the sequence
start_days = [Int(f'start_{i}') for i in range(7)]

# Constraints for sequence: all distinct and in range 0-6
s.add([And(0 <= seq[i], seq[i] < 7) for i in range(7)])
s.add(Distinct(seq))

# Constraints for start_days
for i in range(7):
    if i == 0:
        s.add(start_days[i] >= 1)
    else:
        prev_city = seq[i-1]
        prev_duration = durations[cities[prev_city]]
        s.add(start_days[i] == start_days[i-1] + prev_duration)

# Constraints for fixed cities: Brussels (0), Riga (5), Budapest (4)
for i in range(7):
    # Brussels must start on day 7
    s.add(If(seq[i] == city_to_idx['Brussels'], start_days[i] == 7, True))
    # Riga must start on day 4
    s.add(If(seq[i] == city_to_idx['Riga'], start_days[i] == 4, True))
    # Budapest must start on day 16
    s.add(If(seq[i] == city_to_idx['Budapest'], start_days[i] == 16, True))

# Constraints for allowed flights between consecutive cities
for i in range(6):
    current_city = seq[i]
    next_city = seq[i+1]
    current_city_name = cities[current_city]
    next_city_name = cities[next_city]
    s.add(If(Or([current_city_name == city for city in allowed_flights.keys() if next_city_name in allowed_flights[city]]), True, False))

# Ensure the last city ends on day 17
last_city_idx = seq[6]
last_city_duration = durations[cities[last_city_idx]]
s.add(start_days[6] + last_city_duration - 1 == 17)

# Check if the constraints are satisfiable
if s.check() == sat:
    model = s.model()
    
    # Extract the sequence and start days
    seq_values = [model.evaluate(seq[i]).as_long() for i in range(7)]
    start_days_values = [model.evaluate(start_days[i]).as_long() for i in range(7)]
    
    # Build the itinerary
    itinerary = []
    for i in range(7):
        city_idx = seq_values[i]
        city_name = cities[city_idx]
        start_day = start_days_values[i]
        end_day = start_day + durations[city_name] - 1
        # Add days from start_day to end_day
        for day in range(start_day, end_day + 1):
            itinerary.append({f"Day {day}": city_name})
    
    # Output the JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")