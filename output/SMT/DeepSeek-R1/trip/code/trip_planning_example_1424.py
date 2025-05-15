import z3

# Define cities with their durations and fixed dates where applicable
cities = {
    'Porto': (5, (1, 5)),
    'Amsterdam': (4, (5, 8)),
    'Helsinki': (4, (8, 11)),
    'Naples': (4, (17, 20)),
    'Brussels': (3, (20, 22)),
    'Split': 3,
    'Reykjavik': 5,
    'Lyon': 3,
    'Valencia': 2,
    'Warsaw': 3,
}

# Define flight connections as a set of tuples
flight_pairs = {
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
    ('Porto', 'Warsaw'),
    ('Warsaw', 'Valencia'),
    ('Amsterdam', 'Helsinki'),
    ('Porto', 'Valencia'),
    ('Warsaw', 'Naples'),
    ('Warsaw', 'Brussels'),
    ('Naples', 'Split'),
    ('Helsinki', 'Naples'),
    ('Helsinki', 'Reykjavik'),
    ('Amsterdam', 'Valencia'),
    ('Naples', 'Brussels'),
}

# Helper function to check if two cities are connected
def is_connected(a, b):
    return (a, b) in flight_pairs or (b, a) in flight_pairs

# Initialize solver
solver = z3.Solver()

# Create variables for each city's start and end days
city_vars = {}
fixed_cities = ['Porto', 'Amsterdam', 'Helsinki', 'Naples', 'Brussels']

for city in cities:
    if city in fixed_cities:
        duration, (start, end) = cities[city]
        city_vars[city] = {
            'start': start,
            'end': end,
            'duration': duration
        }
    else:
        duration = cities[city]
        start = z3.Int(f'start_{city}')
        end = z3.Int(f'end_{city}')
        solver.add(start >= 1, end <= 27)
        solver.add(end == start + duration - 1)
        city_vars[city] = {
            'start': start,
            'end': end,
            'duration': duration
        }

# Ensure non-overlapping intervals except for transitions
all_cities = list(cities.keys())
for i in range(len(all_cities)):
    for j in range(i + 1, len(all_cities)):
        c1 = all_cities[i]
        c2 = all_cities[j]
        s1 = city_vars[c1]['start']
        e1 = city_vars[c1]['end']
        s2 = city_vars[c2]['start']
        e2 = city_vars[c2]['end']
        solver.add(z3.Or(e1 < s2, e2 < s1, e1 == s2, e2 == s1))

# Each city (except Porto) must start at the end of a connected city
for city in all_cities:
    if city == 'Porto':
        continue
    current_start = city_vars[city]['start']
    predecessors = []
    for other in all_cities:
        if other == city:
            continue
        other_end = city_vars[other]['end']
        if is_connected(other, city):
            predecessors.append(other_end == current_start)
    solver.add(z3.Or(predecessors))

# Additional constraints for fixed cities' successors and predecessors
# Helsinki's successor starts at 11 and is connected
possible_after_helsinki = [c for c in all_cities if c not in fixed_cities and is_connected('Helsinki', c)]
solver.add(z3.Or([city_vars[c]['start'] == 11 for c in possible_after_helsinki]))

# Naples must be preceded by a city ending at 17 and connected
possible_before_naples = [c for c in all_cities if c not in fixed_cities and is_connected(c, 'Naples')]
solver.add(z3.Or([city_vars[c]['end'] == 17 for c in possible_before_naples]))

# Brussels' successor starts at 22 and is connected
possible_after_brussels = [c for c in all_cities if c not in fixed_cities and is_connected('Brussels', c)]
solver.add(z3.Or([city_vars[c]['start'] == 22 for c in possible_after_brussels]))

# Check solution and print
if solver.check() == z3.sat:
    model = solver.model()
    schedule = []
    for city in all_cities:
        if city in fixed_cities:
            start = city_vars[city]['start']
            end = city_vars[city]['end']
        else:
            start = model[city_vars[city]['start']].as_long()
            end = model[city_vars[city]['end']].as_long()
        schedule.append((city, start, end))
    # Sort by start day
    schedule.sort(key=lambda x: x[1])
    for entry in schedule:
        print(f"{entry[0]}: Days {entry[1]} to {entry[2]}")
else:
    print("No valid itinerary found.")