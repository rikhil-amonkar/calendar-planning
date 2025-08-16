import z3

# Define cities as integers for Z3
PRAGUE = 0
FRANKFURT = 1
NAPLES = 2
HELISNKI = 3  # Corrected from typo
LYON = 4

# Allowed direct flights (start, end)
allowed_flights = [
    (PRAGUE, FRANKFURT), (PRAGUE, LYON), (PRAGUE, HELISNKI),
    (FRANKFURT, PRAGUE), (FRANKFURT, LYON), (FRANKFURT, HELISNKI), (FRANKFURT, NAPLES),
    (HELISNKI, PRAGUE), (HELISNKI, FRANKFURT), (HELISNKI, NAPLES),
    (LYON, PRAGUE), (LYON, FRANKFURT),
    (NAPLES, FRANKFURT), (NAPLES, HELISNKI)
]

# Create Z3 solver
s = z3.Solver()

# Create variables for each day
start = [z3.Int(f'start_{i}') for i in range(12)]
end = [z3.Int(f'end_{i}') for i in range(12)]

# Constraint: end[i] == start[i+1]
for i in range(11):
    s.add(end[i] == start[i + 1])

# Constraint: Day 1 must start in Prague
s.add(start[0] == PRAGUE)

# Constraint: Show in Helsinki from Day 2 to Day 5
for i in range(1, 5):  # Days 2 to 5 (0-based)
    s.add(z3.Or(start[i] == HELISNKI, z3.And(start[i] != end[i], end[i] == HELISNKI)))

# Constraint: Only allow direct flights
for i in range(12):
    s.add(z3.Implies(start[i] != end[i],
                     z3.Or([z3.And(start[i] == a, end[i] == b) for a, b in allowed_flights])))

# Count how many days each city is visited
count_prague = 0
count_frankfurt = 0
count_naples = 0
count_helsinki = 0
count_lyon = 0

for i in range(12):
    count_prague += z3.If(start[i] == PRAGUE, 1, 0)
    count_frankfurt += z3.If(start[i] == FRANKFURT, 1, 0)
    count_naples += z3.If(start[i] == NAPLES, 1, 0)
    count_helsinki += z3.If(start[i] == HELISNKI, 1, 0)
    count_lyon += z3.If(start[i] == LYON, 1, 0)

for i in range(12):
    count_prague += z3.If(z3.And(start[i] != end[i], end[i] == PRAGUE), 1, 0)
    count_frankfurt += z3.If(z3.And(start[i] != end[i], end[i] == FRANKFURT), 1, 0)
    count_naples += z3.If(z3.And(start[i] != end[i], end[i] == NAPLES), 1, 0)
    count_helsinki += z3.If(z3.And(start[i] != end[i], end[i] == HELISNKI), 1, 0)
    count_lyon += z3.If(z3.And(start[i] != end[i], end[i] == LYON), 1, 0)

# Required visit durations
s.add(count_prague == 2)
s.add(count_frankfurt == 3)
s.add(count_naples == 4)
s.add(count_helsinki == 4)
s.add(count_lyon == 3)

# Solve
if s.check() == z3.sat:
    model = s.model()
    cities = ['Prague', 'Frankfurt', 'Naples', 'Helsinki', 'Lyon']
    itinerary = [{'day': i + 1, 'city': cities[model.evaluate(end[i]).as_long()]} for i in range(12)]
    print(json.dumps({'itinerary': itinerary}, indent=2))
else:
    print("No solution found.")