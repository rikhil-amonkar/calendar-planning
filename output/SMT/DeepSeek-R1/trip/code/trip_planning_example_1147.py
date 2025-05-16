from z3 import *

# Define city codes and required days
cities = {
    'Istanbul': 0,
    'Brussels': 1,
    'Helsinki': 2,
    'Split': 3,
    'Dubrovnik': 4,
    'Milan': 5,
    'Frankfurt': 6,
    'Vilnius': 7
}

required_days = {
    1: 3,  # Brussels
    2: 3,  # Helsinki
    3: 4,  # Split
    4: 2,  # Dubrovnik
    5: 4,  # Milan
    6: 3,  # Frankfurt
    7: 5,  # Vilnius
    0: 5   # Istanbul
}

# Direct flights between cities (from, to)
flights = [
    (0,1), (0,2), (0,5), (0,6), (0,7),
    (1,5), (1,2), (1,6),
    (2,1), (2,3), (2,4), (2,5), (2,6),
    (3,5), (3,2), (3,6),
    (4,6),
    (5,1), (5,3), (5,2), (5,6),
    (6,7)
]

s = Solver()

# Sequence of 5 cities between Istanbul and Frankfurt
sequence = [Int(f's_{i}') for i in range(5)]
for city in sequence:
    s.add(Or([city == c for c in [1, 2, 3, 4, 5]]))
s.add(Distinct(sequence))

# Dubrovnik (4) can only be in the last position
for i in range(4):
    s.add(sequence[i] != 4)

# First city must be reachable from Istanbul
s.add(Or(sequence[0] == 1, sequence[0] == 2, sequence[0] == 5))

# Last city must have a flight to Frankfurt
valid_last = Or(*[sequence[4] == c for c in [1, 2, 3, 4, 5]])
s.add(valid_last)

# Flight constraints between consecutive cities
for i in range(4):
    current = sequence[i]
    next_city = sequence[i+1]
    valid_flight = Or([And(current == f[0], next_city == f[1]) for f in flights if f[0] in [1,2,3,4,5] and f[1] in [1,2,3,4,5]])
    s.add(valid_flight)

# Start and end days for each city in the sequence
start = [Int(f'start_{i}') for i in range(5)]
end = [Int(f'end_{i}') for i in range(5)]
s.add(start[0] == 5)  # Start from day 5

# Required days for each city in the sequence
required = [If(sequence[i] == 1, 3,
              If(sequence[i] == 2, 3,
               If(sequence[i] == 3, 4,
                If(sequence[i] == 4, 2,
                 4)))) for i in range(5)]

for i in range(5):
    s.add(end[i] == start[i] + required[i] - 1)
for i in range(1, 5):
    s.add(start[i] == end[i-1])

# Last city must end on day 16 to transition to Frankfurt
s.add(end[4] == 16)

if s.check() == sat:
    m = s.model()
    seq = [m.evaluate(city).as_long() for city in sequence]
    start_days = [m.evaluate(s).as_long() for s in start]
    end_days = [m.evaluate(e).as_long() for e in end]
    
    city_names = {v: k for k, v in cities.items()}
    itinerary = [
        ('Istanbul', 1, 5),
        *[(city_names[seq[i]], start_days[i], end_days[i]) for i in range(5)],
        ('Frankfurt', 16, 18),
        ('Vilnius', 18, 22)
    ]
    
    print("Day Plan:")
    for entry in itinerary:
        print(f"Stay in {entry[0]} from day {entry[1]} to day {entry[2]}")
else:
    print("No valid plan found.")