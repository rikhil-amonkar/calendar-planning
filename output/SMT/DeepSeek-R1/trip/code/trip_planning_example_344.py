from z3 import *

# Define cities and their required durations
cities = {
    'Valencia': 6,
    'Athens': 6,
    'Naples': 5,
    'Zurich': 6
}

# Fixed dates
fixed = {
    'Athens': (1, 6),
    'Naples': (16, 20)
}

# Direct flight pairs (bidirectional)
flight_pairs = [
    ('Valencia', 'Naples'),
    ('Valencia', 'Athens'),
    ('Athens', 'Naples'),
    ('Zurich', 'Naples'),
    ('Athens', 'Zurich'),
    ('Zurich', 'Valencia')
]

# Build direct_flights dictionary
direct_flights = {city: [] for city in cities}
for a, b in flight_pairs:
    direct_flights[a].append(b)
    direct_flights[b].append(a)

# Create solver
s = Solver()

# Create start and end day variables for each city
start = {city: Int(f'start_{city}') for city in cities}
end = {city: Int(f'end_{city}') for city in cities}

# Add duration constraints
for city in cities:
    s.add(end[city] == start[city] + cities[city] - 1)

# Fixed dates constraints
for city, (fixed_start, fixed_end) in fixed.items():
    s.add(start[city] == fixed_start)
    s.add(end[city] == fixed_end)

# All cities have valid start and end days within 20-day trip
for city in cities:
    s.add(start[city] >= 1)
    s.add(end[city] <= 20)

# No overlapping stays between any two cities
for c1 in cities:
    for c2 in cities:
        if c1 != c2:
            s.add(Or(end[c1] < start[c2], end[c2] < start[c1]))

# Flight connectivity between consecutive cities based on schedule order
ordered_cities = sorted(cities.keys(), key=lambda x: start[x])
for i in range(len(ordered_cities) - 1):
    current = ordered_cities[i]
    next_city = ordered_cities[i+1]
    s.add(Or([next_city in direct_flights[current]]))

# Check for valid solution
if s.check() == sat:
    m = s.model()
    schedule = []
    for city in cities:
        schedule.append((city, m.eval(start[city]).as_long(), m.eval(end[city]).as_long()))
    schedule.sort(key=lambda x: x[1])
    print("Valid trip plan:")
    for entry in schedule:
        print(f"{entry[0]}: Days {entry[1]} to {entry[2]}")
else:
    print("No valid trip plan exists. The total required days exceed 20 or flight connections are insufficient.")