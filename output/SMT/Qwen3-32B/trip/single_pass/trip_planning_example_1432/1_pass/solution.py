from z3 import *
import json

# Define city IDs
STOCKHOLM = 0
VALENCIA = 1
VIENNA = 2
ATHENS = 3
RIGA = 4
FRANKFURT = 5
SALZBURG = 6
REYKJAVIK = 7
BUCHAREST = 8
AMSTERDAM = 9

# Allowed transitions (both directions)
allowed_transitions = set()
allowed_transitions.add((VALENCIA, FRANKFURT)), allowed_transitions.add((FRANKFURT, VALENCIA))
allowed_transitions.add((VIENNA, BUCHAREST)), allowed_transitions.add((BUCHAREST, VIENNA))
allowed_transitions.add((VALENCIA, ATHENS)), allowed_transitions.add((ATHENS, VALENCIA))
allowed_transitions.add((ATHENS, BUCHAREST)), allowed_transitions.add((BUCHAREST, ATHENS))
allowed_transitions.add((RIGA, FRANKFURT)), allowed_transitions.add((FRANKFURT, RIGA))
allowed_transitions.add((STOCKHOLM, ATHENS)), allowed_transitions.add((ATHENS, STOCKHOLM))
allowed_transitions.add((AMSTERDAM, BUCHAREST)), allowed_transitions.add((BUCHAREST, AMSTERDAM))
allowed_transitions.add((ATHENS, RIGA)), allowed_transitions.add((RIGA, ATHENS))
allowed_transitions.add((AMSTERDAM, FRANKFURT)), allowed_transitions.add((FRANKFURT, AMSTERDAM))
allowed_transitions.add((STOCKHOLM, VIENNA)), allowed_transitions.add((VIENNA, STOCKHOLM))
allowed_transitions.add((VIENNA, RIGA)), allowed_transitions.add((RIGA, VIENNA))
allowed_transitions.add((AMSTERDAM, REYKJAVIK)), allowed_transitions.add((REYKJAVIK, AMSTERDAM))
allowed_transitions.add((REYKJAVIK, FRANKFURT)), allowed_transitions.add((FRANKFURT, REYKJAVIK))
allowed_transitions.add((STOCKHOLM, AMSTERDAM)), allowed_transitions.add((AMSTERDAM, STOCKHOLM))
allowed_transitions.add((AMSTERDAM, VALENCIA)), allowed_transitions.add((VALENCIA, AMSTERDAM))
allowed_transitions.add((VIENNA, FRANKFURT)), allowed_transitions.add((FRANKFURT, VIENNA))
allowed_transitions.add((VALENCIA, BUCHAREST)), allowed_transitions.add((BUCHAREST, VALENCIA))
allowed_transitions.add((BUCHAREST, FRANKFURT)), allowed_transitions.add((FRANKFURT, BUCHAREST))
allowed_transitions.add((STOCKHOLM, FRANKFURT)), allowed_transitions.add((FRANKFURT, STOCKHOLM))
allowed_transitions.add((VALENCIA, VIENNA)), allowed_transitions.add((VIENNA, VALENCIA))
allowed_transitions.add((REYKJAVIK, ATHENS)), allowed_transitions.add((ATHENS, REYKJAVIK))
allowed_transitions.add((FRANKFURT, SALZBURG)), allowed_transitions.add((SALZBURG, FRANKFURT))
allowed_transitions.add((AMSTERDAM, VIENNA)), allowed_transitions.add((VIENNA, AMSTERDAM))
allowed_transitions.add((STOCKHOLM, RIGA)), allowed_transitions.add((RIGA, STOCKHOLM))
allowed_transitions.add((AMSTERDAM, RIGA)), allowed_transitions.add((RIGA, AMSTERDAM))
allowed_transitions.add((VIENNA, REYKJAVIK)), allowed_transitions.add((REYKJAVIK, VIENNA))
allowed_transitions.add((AMSTERDAM, ATHENS)), allowed_transitions.add((ATHENS, AMSTERDAM))
allowed_transitions.add((ATHENS, FRANKFURT)), allowed_transitions.add((FRANKFURT, ATHENS))
allowed_transitions.add((VIENNA, ATHENS)), allowed_transitions.add((ATHENS, VIENNA))
allowed_transitions.add((RIGA, BUCHAREST)), allowed_transitions.add((BUCHAREST, RIGA))

# Create Z3 solver
s = Solver()

# Sequence of cities
seq = [Int(f'seq_{i}') for i in range(10)]
s.add(Distinct(seq))
for city in seq:
    s.add(And(0 <= city, city <= 9))
s.add(seq[0] == STOCKHOLM)

# Add transition constraints
for i in range(9):
    from_city = seq[i]
    to_city = seq[i+1]
    allowed_expr = Or([And(from_city == a, to_city == b) for (a, b) in allowed_transitions])
    s.add(allowed_expr)

# Start and end days for each position in the sequence
start_days = [Int(f'start_{i}') for i in range(10)]
end_days = [Int(f'end_{i}') for i in range(10)]

# First city constraints
s.add(start_days[0] == 1)
s.add(end_days[0] == 3)

# Link start and end days
for i in range(1, 10):
    s.add(start_days[i] == end_days[i-1])

# Duration constraints
durations = {
    0: 3,  # STOCKHOLM
    1: 2,  # VALENCIA
    2: 5,  # VIENNA
    3: 5,  # ATHENS
    4: 3,  # RIGA
    5: 4,  # FRANKFURT
    6: 5,  # SALZBURG
    7: 5,  # REYKJAVIK
    8: 3,  # BUCHAREST
    9: 3,  # AMSTERDAM
}

for i in range(10):
    city = seq[i]
    duration = durations[city]
    s.add(end_days[i] == start_days[i] + duration - 1)

# Fixed city constraints
fixed_start = {
    0: 1,  # STOCKHOLM
    1: 5,  # VALENCIA
    2: 6,  # VIENNA
    3: 14, # ATHENS
    4: 18, # RIGA
}

fixed_end = {
    0: 3,  # STOCKHOLM
    1: 6,  # VALENCIA
    2: 10, # VIENNA
    3: 18, # ATHENS
    4: 20, # RIGA
}

for i in range(10):
    city = seq[i]
    for c in fixed_start.keys():
        s.add(Implies(city == c, start_days[i] == fixed_start[c]))
        s.add(Implies(city == c, end_days[i] == fixed_end[c]))

# Final day constraint
s.add(end_days[9] == 29)

# Solve and generate itinerary
if s.check() == sat:
    m = s.model()
    sequence = [m.evaluate(seq[i]).as_long() for i in range(10)]
    city_names = {
        0: "Stockholm",
        1: "Valencia",
        2: "Vienna",
        3: "Athens",
        4: "Riga",
        5: "Frankfurt",
        6: "Salzburg",
        7: "Reykjavik",
        8: "Bucharest",
        9: "Amsterdam",
    }
    itinerary = []
    for i in range(10):
        city_id = sequence[i]
        city_name = city_names[city_id]
        start = m.evaluate(start_days[i]).as_long()
        end = m.evaluate(end_days[i]).as_long()
        for day in range(start, end + 1):
            itinerary.append({day: city_name})
    print(json.dumps({'itinerary': itinerary}, indent=2))
else:
    print("No solution found.")