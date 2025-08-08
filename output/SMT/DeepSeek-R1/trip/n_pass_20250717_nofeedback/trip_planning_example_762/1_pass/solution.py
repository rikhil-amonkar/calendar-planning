from z3 import *

# Define the city mappings
cities = ['Dublin', 'Madrid', 'Oslo', 'London', 'Vilnius', 'Berlin']
mapping = {city: idx for idx, city in enumerate(cities)}
rev_mapping = {idx: city for idx, city in enumerate(cities)}

# Direct flights (both directions included)
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

# Create set of allowed consecutive city pairs (including same city and direct flights)
allowed_consecutive = set()
for a, b in flights:
    a_idx = mapping[a]
    b_idx = mapping[b]
    allowed_consecutive.add((a_idx, b_idx))
    allowed_consecutive.add((b_idx, a_idx))
for i in range(6):
    allowed_consecutive.add((i, i))

# Create Z3 variables for each day (c1 to c13)
c = [Int('c_%d' % i) for i in range(1, 14)]
solver = Solver()

# Each day variable must be between 0 and 5 (inclusive)
for i in range(13):
    solver.add(And(c[i] >= 0, c[i] <= 5))

# Flight constraints: consecutive days must be in allowed_consecutive
for i in range(12):
    conds = []
    for (a, b) in allowed_consecutive:
        conds.append(And(c[i] == a, c[i+1] == b))
    solver.add(Or(conds))

# Counting constraints for each city
counts = [0] * 6
for city in range(6):
    term1 = Sum([If(c[i] == city, 1, 0) for i in range(13)])  # count as end city
    term2 = Sum([If(And(c[i] == city, c[i] != c[i+1]), 1, 0) for i in range(12)])  # count as start city when leaving next day
    counts[city] = term1 + term2

# Set the required days for each city
solver.add(counts[mapping['Dublin']] == 3)
solver.add(counts[mapping['Madrid']] == 2)
solver.add(counts[mapping['Oslo']] == 3)
solver.add(counts[mapping['London']] == 2)
solver.add(counts[mapping['Vilnius']] == 3)
solver.add(counts[mapping['Berlin']] == 5)

# Event constraints
# Dublin: must be in Dublin on at least one day between 7 and 9 (inclusive)
# This means: either at the beginning of day 7 (c6) or at the end of day7 (c7) or ... up to end of day9 (c9)
solver.add(Or(c[5] == mapping['Dublin'],  # c6 (beginning of day7)
             c[6] == mapping['Dublin'],   # c7 (end of day7)
             c[7] == mapping['Dublin'],   # c8 (end of day8)
             c[8] == mapping['Dublin']))  # c9 (end of day9)

# Madrid: must be in Madrid on at least one day between 2 and 3 (inclusive)
solver.add(Or(c[0] == mapping['Madrid'],  # c1 (beginning of day2 if leaving on day2, or end of day1 if staying)
             c[1] == mapping['Madrid'],   # c2 (end of day2)
             c[2] == mapping['Madrid']))  # c3 (end of day3)

# Berlin: must be in Berlin on at least one day between 3 and 7 (inclusive)
solver.add(Or(c[1] == mapping['Berlin'],   # c2 (beginning of day3)
             c[2] == mapping['Berlin'],    # c3 (end of day3)
             c[3] == mapping['Berlin'],    # c4 (end of day4)
             c[4] == mapping['Berlin'],    # c5 (end of day5)
             c[5] == mapping['Berlin'],    # c6 (end of day6)
             c[6] == mapping['Berlin']))   # c7 (end of day7)

# Check and get the model
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(13):
        city_idx = model.evaluate(c[i]).as_long()
        city_name = rev_mapping[city_idx]
        itinerary.append({"day": i+1, "place": city_name})
    result = {'itinerary': itinerary}
    print(result)
else:
    print("No solution found")