from z3 import *

# Define cities
DUBROVNIK = 0
WARSAW = 1
STUTTGART = 2
BUCHAREST = 3
COPENHAGEN = 4

# Durations for each city
def get_duration(city):
    return If(city == DUBROVNIK, 5,
              If(city == WARSAW, 2,
                 If(city == STUTTGART, 7,
                    If(city == BUCHAREST, 6, 3))))

# Create Z3 solver
solver = Solver()

# Create sequence variables
c = [Int(f'c{i}') for i in range(5)]
solver.add(Distinct(c))
for city in c:
    solver.add(And(0 <= city, city <= 4))

# Create start_day variables
s = [Int(f's{i}') for i in range(5)]
solver.add(s[0] == 1)

# Add constraints for start_day[i] based on previous city's duration
for i in range(1, 5):
    prev_city = c[i - 1]
    duration_prev = get_duration(prev_city)
    solver.add(s[i] == s[i - 1] + duration_prev - 1)

# Add transition constraints between consecutive cities
allowed_transitions = [
    (WARSAW, COPENHAGEN), (COPENHAGEN, WARSAW),
    (STUTTGART, COPENHAGEN), (COPENHAGEN, STUTTGART),
    (WARSAW, STUTTGART), (STUTTGART, WARSAW),
    (BUCHAREST, COPENHAGEN), (COPENHAGEN, BUCHAREST),
    (BUCHAREST, WARSAW), (WARSAW, BUCHAREST),
    (COPENHAGEN, DUBROVNIK), (DUBROVNIK, COPENHAGEN)
]

for i in range(4):
    current_city = c[i]
    next_city = c[i + 1]
    allowed_pairs = [And(current_city == a, next_city == b) for a, b in allowed_transitions]
    solver.add(Or(allowed_pairs))

# Add constraints for Stuttgart and Bucharest
for i in range(5):
    current_city = c[i]
    # Stuttgart constraints
    solver.add(Implies(current_city == STUTTGART,
                       And(7 >= s[i], 7 <= s[i] + 7 - 1,
                           13 >= s[i], 13 <= s[i] + 7 - 1)))
    # Bucharest wedding constraint: must start on or before day 6
    solver.add(Implies(current_city == BUCHAREST, s[i] <= 6))

# Check for solution
if solver.check() == sat:
    model = solver.model()
    # Extract the sequence
    sequence = [model.evaluate(c[i]).as_long() for i in range(5)]
    start_days = [model.evaluate(s[i]).as_long() for i in range(5)]
    # Map city codes to names
    city_names = {0: 'Dubrovnik', 1: 'Warsaw', 2: 'Stuttgart', 3: 'Bucharest', 4: 'Copenhagen'}
    # Build itinerary
    itinerary = []
    for i in range(5):
        city_code = sequence[i]
        city_name = city_names[city_code]
        start = start_days[i]
        duration = {0: 5, 1: 2, 2: 7, 3: 6, 4: 3}[city_code]
        end = start + duration - 1
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city_name})
    # Output as JSON
    import json
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")