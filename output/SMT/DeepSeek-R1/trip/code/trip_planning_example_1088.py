from z3 import *

# Define cities and their required durations
cities = {
    'Reykjavik': 2,
    'Oslo': 5,
    'Stuttgart': 5,
    'Split': 3,
    'Geneva': 2,
    'Porto': 3,
    'Tallinn': 5,
    'Stockholm': 3
}

# Fixed dates
fixed = {
    'Reykjavik': (1, 2),
    'Porto': (19, 21)
}

# Direct flights (bidirectional)
direct_flights = {
    'Reykjavik': ['Stuttgart', 'Stockholm', 'Tallinn', 'Oslo'],
    'Oslo': ['Stockholm', 'Stuttgart', 'Split', 'Geneva', 'Porto', 'Tallinn', 'Reykjavik'],
    'Stuttgart': ['Porto', 'Stockholm', 'Reykjavik', 'Split'],
    'Split': ['Stuttgart', 'Oslo', 'Geneva', 'Stockholm'],
    'Geneva': ['Oslo', 'Porto', 'Split', 'Stockholm'],
    'Porto': ['Stuttgart', 'Geneva', 'Oslo'],
    'Tallinn': ['Reykjavik', 'Oslo'],
    'Stockholm': ['Oslo', 'Stuttgart', 'Reykjavik', 'Split', 'Geneva']
}

# Create solver
s = Solver()

# Create start and end day variables for each city
start = {city: Int(f'start_{city}') for city in cities}
end = {city: Int(f'end_{city}') for city in cities}

# Add duration constraints
for city in cities:
    s.add(end[city] == start[city] + cities[city] - 1)

# Fixed dates
s.add(start['Reykjavik'] == 1)
s.add(end['Reykjavik'] == 2)
s.add(start['Porto'] == 19)
s.add(end['Porto'] == 21)

# Stockholm must be between day 2 and 4
s.add(start['Stockholm'] <= 4)
s.add(end['Stockholm'] >= 2)

# All cities have positive start days and end <= 21
for city in cities:
    s.add(start[city] >= 1)
    s.add(end[city] <= 21)

# Cities' stays do not overlap
for c1 in cities:
    for c2 in cities:
        if c1 != c2:
            s.add(Or(end[c1] < start[c2], end[c2] < start[c1]))

# Flights between consecutive cities (based on start days)
# Determine the order of cities by start day
# For each pair of cities (c1, c2), if c1 is before c2, there must be a flight from c1 to c2 or vice versa
# This is a simplified approach and may not cover all cases, but it's a starting point

# Create a list of cities sorted by start day
order = sorted(cities.keys(), key=lambda x: start[x])

# Ensure consecutive cities in the order have direct flights
for i in range(len(order) - 1):
    current = order[i]
    next_city = order[i+1]
    s.add(Or([current == c for c in direct_flights.get(next_city, [])] + [next_city == c for c in direct_flights.get(current, [])]))

# Check if the solution is satisfiable
if s.check() == sat:
    m = s.model()
    # Print the schedule
    schedule = []
    for city in cities:
        schedule.append((city, m.eval(start[city]), m.eval(end[city]))
    # Sort by start day
    schedule.sort(key=lambda x: x[1])
    print("Trip plan:")
    for entry in schedule:
        print(f"{entry[0]}: Days {entry[1]} to {entry[2]}")
else:
    print("No valid trip plan exists.")