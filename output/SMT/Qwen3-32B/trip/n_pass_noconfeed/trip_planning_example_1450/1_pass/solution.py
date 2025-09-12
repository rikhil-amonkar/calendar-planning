import z3
import json

# Define cities and their codes
# 0: Stockholm, 1: Hamburg, 2: Florence, 3: Istanbul, 4: Oslo, 5: Vilnius, 6: Santorini, 7: Munich, 8: Frankfurt, 9: Krakow
durations = [3, 5, 2, 5, 5, 5, 2, 5, 4, 5]

allowed_transitions = [
    (4, 0), (0, 4),
    (9, 8), (8, 9),
    (9, 3), (3, 9),
    (7, 0), (0, 7),
    (1, 0), (0, 1),
    (9, 5),
    (4, 3), (3, 4),
    (3, 0), (0, 3),
    (4, 9), (9, 4),
    (5, 3), (3, 5),
    (4, 5), (5, 4),
    (8, 3), (3, 8),
    (4, 8), (8, 4),
    (7, 1), (1, 7),
    (7, 3), (3, 7),
    (4, 7), (7, 4),
    (8, 2), (2, 8),
    (4, 1), (1, 4),
    (5, 8), (8, 5),
    (2, 7),
    (9, 7), (7, 9),
    (1, 3), (3, 1),
    (8, 0), (0, 8),
    (0, 6),
    (8, 7), (7, 8),
    (6, 4),
    (9, 0), (0, 9),
    (5, 7),
    (8, 1), (1, 8),
]

solver = z3.Solver()

# Variables for city positions (0 to 9)
city_pos = [z3.Int(f'city_pos_{i}') for i in range(10)]

# All cities are distinct
solver.add(z3.Distinct(city_pos))

# Each city is between 0 and 9
for c in city_pos:
    solver.add(z3.And(c >= 0, c <= 9))

# Constraints for allowed transitions between consecutive cities
for i in range(9):
    current = city_pos[i]
    next_city = city_pos[i+1]
    constraints = []
    for (a, b) in allowed_transitions:
        constraints.append(z3.And(current == a, next_city == b))
    solver.add(z3.Or(constraints))

# Variables for start days
start_day = [z3.Int(f'start_day_{i}') for i in range(10)]

# First day is 1
solver.add(start_day[0] == 1)

# Function to get duration based on city code
def get_duration(city_code):
    return z3.If(city_code == 0, 3,
        z3.If(city_code == 1, 5,
        z3.If(city_code == 2, 2,
        z3.If(city_code == 3, 5,
        z3.If(city_code == 4, 5,
        z3.If(city_code == 5, 5,
        z3.If(city_code == 6, 2,
        z3.If(city_code == 7, 5,
        z3.If(city_code == 8, 4,
        z3.If(city_code == 9, 5, 0)))))))))

# Constraints for start_day[i] based on previous start_day and duration
for i in range(1, 10):
    prev_city = city_pos[i-1]
    duration_prev = get_duration(prev_city)
    solver.add(start_day[i] == start_day[i-1] + duration_prev - 1)

# Constraints for Krakow (code 9) to start on day 5
for k in range(10):
    solver.add(z3.Implies(city_pos[k] == 9, start_day[k] == 5))

# Constraints for Istanbul (code 3) to start on day 25
for i in range(10):
    solver.add(z3.Implies(city_pos[i] == 3, start_day[i] == 25))

# Check if the solver can find a solution
if solver.check() == z3.sat:
    model = solver.model()
    # Extract city sequence and start days
    city_sequence = [model.eval(city_pos[i]).as_long() for i in range(10)]
    start_days = [model.eval(start_day[i]).as_long() for i in range(10)]
    
    # Map city codes to names
    city_names = {
        0: "Stockholm",
        1: "Hamburg",
        2: "Florence",
        3: "Istanbul",
        4: "Oslo",
        5: "Vilnius",
        6: "Santorini",
        7: "Munich",
        8: "Frankfurt",
        9: "Krakow"
    }
    
    # Generate the itinerary
    itinerary = []
    for i in range(10):
        city_code = city_sequence[i]
        city_name = city_names[city_code]
        duration = durations[city_code]
        start = start_days[i]
        end = start + duration - 1
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city_name})
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")