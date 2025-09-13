import json
from z3 import *

# Define cities and their indices
cities = ['Frankfurt', 'Manchester', 'Valencia', 'Naples', 'Oslo', 'Vilnius']
city_to_idx = {city: idx for idx, city in enumerate(cities)}
frankfurt_idx = 0
vilnius_idx = 5

# Define direct flights as pairs of indices
direct_flight_pairs = [
    ('Valencia', 'Frankfurt'),
    ('Manchester', 'Frankfurt'),
    ('Naples', 'Manchester'),
    ('Naples', 'Frankfurt'),
    ('Naples', 'Oslo'),
    ('Oslo', 'Frankfurt'),
    ('Vilnius', 'Frankfurt'),
    ('Oslo', 'Vilnius'),
    ('Manchester', 'Oslo'),
    ('Valencia', 'Naples'),
]

direct_flights = set()
for a, b in direct_flight_pairs:
    a_idx = city_to_idx[a]
    b_idx = city_to_idx[b]
    direct_flights.add((a_idx, b_idx))
    direct_flights.add((b_idx, a_idx))

# Create Z3 variables for each day's city (0-based index for days 1-16)
days = 16
day_city = [Int(f'day_{i+1}') for i in range(days)]  # day_city[0] is day 1, ..., day_city[15] is day 16

s = Solver()

# Constraint: day 12 is Vilnius (index 11 for day 12)
s.add(day_city[11] == vilnius_idx)

# Constraint: days 13-16 are Frankfurt (indices 12, 13, 14, 15 for days 13-16)
frankfurt_idx = 0
for i in range(12, 16):
    s.add(day_city[i] == frankfurt_idx)

# Constraints for consecutive days: if current != next, then (current, next) is a direct flight
direct_flights_list = list(direct_flights)
for i in range(15):  # i ranges from 0 to 14 (days 1-15)
    current = day_city[i]
    next_day = day_city[i+1]
    # current == next_day OR (current, next_day) is in direct_flights
    flight_allowed = Or([And(current == a, next_day == b) for a, b in direct_flights_list])
    s.add(Or(current == next_day, flight_allowed))

# Required days for each city (excluding Frankfurt which is already fixed)
required_days = {
    1: 4,  # Manchester
    2: 4,  # Valencia
    3: 4,  # Naples
    4: 3,  # Oslo
    5: 2,  # Vilnius
}

for c in required_days:
    sum_expr = 0
    for i in range(15):  # days 1-15
        current = day_city[i]
        next_day = day_city[i+1]
        sum_expr += If(current == c, 1, 0) + If(next_day == c, 1, 0)
    # Add contribution from day 16
    sum_expr += If(day_city[15] == c, 1, 0)
    s.add(sum_expr == required_days[c])

# Check for solution
if s.check() == sat:
    m = s.model()
    day_values = [m.eval(day_city[i]).as_long() for i in range(16)]
    
    # Group consecutive days
    groups = []
    current_city = day_values[0]
    start_day = 1
    for i in range(1, 16):
        if day_values[i] != current_city:
            end_day = i
            groups.append( (start_day, end_day, current_city) )
            current_city = day_values[i]
            start_day = i + 1
    # Add the last group
    groups.append( (start_day, 16, current_city) )
    
    # Convert to itinerary
    itinerary = []
    for start, end, city_idx in groups:
        city_name = cities[city_idx]
        day_range = f"Day {start}-{end}"
        itinerary.append( {"day_range": day_range, "place": city_name} )
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")