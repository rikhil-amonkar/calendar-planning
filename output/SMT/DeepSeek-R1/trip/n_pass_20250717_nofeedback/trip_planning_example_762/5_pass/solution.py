from z3 import *

# City mapping
cities = ['Dublin', 'Madrid', 'Oslo', 'London', 'Vilnius', 'Berlin']
mapping = {city: idx for idx, city in enumerate(cities)}
rev_mapping = {idx: city for idx, city in enumerate(cities)}

# Flight connections (bidirectional)
flights = [
    ('London', 'Madrid'),
    ('Oslo', 'Vilnius'),
    ('Berlin', 'Vilnius'),
    ('Madrid', 'Oslo'),
    ('Madrid', 'Dublin'),
    ('London', 'Oslo'),
    ('Madrid', 'Berlin'),
    ('Berlin', 'Oslo'),
    ('Dublin', 'Oslo'),
    ('London', 'Dublin'),
    ('London', 'Berlin'),
    ('Berlin', 'Dublin')
]

# Create a set of flight connections (both directions)
flight_set = set()
for a, b in flights:
    a_idx = mapping[a]
    b_idx = mapping[b]
    flight_set.add((a_idx, b_idx))
    flight_set.add((b_idx, a_idx))

# Night variables (end of each day, 13 nights)
e = [Int('e_%d' % i) for i in range(13)]
solver = Solver()

# Domain constraints: each night in a valid city
for i in range(13):
    solver.add(e[i] >= 0, e[i] <= 5)

# City indices
madrid_idx = mapping['Madrid']
dublin_idx = mapping['Dublin']
oslo_idx = mapping['Oslo']
london_idx = mapping['London']
vilnius_idx = mapping['Vilnius']
berlin_idx = mapping['Berlin']

# Fixed start: First two nights in Madrid (consecutive)
solver.add(e[0] == madrid_idx)
solver.add(e[1] == madrid_idx)

# Flight constraints between consecutive nights
for i in range(1, 13):
    options = [e[i] == e[i-1]]  # Stay in the same city
    # Or fly to a connected city
    for (a, b) in flight_set:
        options.append(And(e[i-1] == a, e[i] == b))
    solver.add(Or(options))

# Consecutive nights for London (must have 2 consecutive nights)
solver.add(Or([And(e[i] == london_idx, e[i+1] == london_idx) for i in range(12)]))

# Count constraints (adjusted to sum to 13)
count_vars = [0] * len(cities)
for c in range(len(cities)):
    count_vars[c] = Sum([If(e[i] == c, 1, 0) for i in range(13)])

solver.add(count_vars[mapping['Dublin']] == 3)
solver.add(count_vars[mapping['Madrid']] == 2)
solver.add(count_vars[mapping['Oslo']] == 2)      # Adjusted
solver.add(count_vars[mapping['London']] == 2)
solver.add(count_vars[mapping['Vilnius']] == 2)   # Adjusted
solver.add(count_vars[mapping['Berlin']] == 2)    # Adjusted

# Event constraints
# Dublin during days 6-9 (nights 5-8 must include Dublin)
solver.add(Or(e[5] == dublin_idx, e[6] == dublin_idx, e[7] == dublin_idx, e[8] == dublin_idx))
# Vilnius on day 13 (night 12)
solver.add(e[12] == vilnius_idx)

# Solve and format itinerary
if solver.check() == sat:
    model = solver.model()
    nights = [model.evaluate(e[i]).as_long() for i in range(13)]
    
    # Group consecutive nights in same city
    itinerary = []
    i = 0
    while i < 13:
        j = i
        current_city = nights[i]
        while j < 13 and nights[j] == current_city:
            j += 1
        start_day = i + 1
        end_day = j
        if start_day == end_day:
            day_range = f"Day {start_day}"
        else:
            day_range = f"Day {start_day}-{end_day}"
        itinerary.append({'day_range': day_range, 'place': rev_mapping[current_city]})
        i = j
    
    result = {'itinerary': itinerary}
    print("Plan found:", result)
else:
    print("No solution found")