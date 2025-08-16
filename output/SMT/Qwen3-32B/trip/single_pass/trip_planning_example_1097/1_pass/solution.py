from z3 import *
import json

# Define city codes and their names
city_names = {
    0: "Reykjavik",
    1: "Riga",
    2: "Oslo",
    3: "Lyon",
    4: "Dubrovnik",
    5: "Madrid",
    6: "Warsaw",
    7: "London",
}

# Durations for each city
durations = [4, 2, 3, 5, 2, 2, 4, 3]  # index 0-7

# Allowed flight pairs (A, B)
allowed_pairs = [
    (6,0), (0,6),
    (2,5), (5,2),
    (6,1), (1,6),
    (3,7), (7,3),
    (5,7), (7,5),
    (6,7), (7,6),
    (0,5), (0,6), (0,2),
    (2,4), (4,2),
    (2,0), (0,2),
    (1,2), (2,1),
    (2,3), (3,2),
    (2,7), (7,2),
    (7,0), (0,7),
    (6,5), (5,6),
    (5,3), (3,5),
    (4,5), (5,4),
]

# Create solver instance
s = Solver()

# Create variables for the cities sequence and start days
city_vars = [Int(f'city_{i}') for i in range(8)]
start_day_vars = [Int(f'start_day_{i}') for i in range(8)]

# All cities are distinct
s.add(Distinct(city_vars))

# Cities are in 0-7
for c in city_vars:
    s.add(And(0 <= c, c <= 7))

# Start day constraints
s.add(start_day_vars[0] == 1)

for i in range(1, 8):
    prev_city = city_vars[i-1]
    # Function to get duration based on city code
    def get_duration(c):
        return If(c == 0, 4,
            If(c == 1, 2,
                If(c == 2, 3,
                    If(c == 3, 5,
                        If(c == 4, 2,
                            If(c == 5, 2,
                                If(c == 6, 4, 3)
                            )
                        )
                    )
                )
            )
        )
    duration_prev = get_duration(prev_city)
    s.add(start_day_vars[i] == start_day_vars[i-1] + duration_prev)

# Add transition constraints
for i in range(7):
    current = city_vars[i]
    next_city = city_vars[i+1]
    allowed = []
    for a, b in allowed_pairs:
        allowed.append(And(current == a, next_city == b))
    s.add(Or(allowed))

# Add Riga and Dubrovnik constraints
for i in range(8):
    s.add(Implies(city_vars[i] == 1, Or(start_day_vars[i] == 3, start_day_vars[i] == 4, start_day_vars[i] == 5)))
    s.add(Implies(city_vars[i] == 4, Or(start_day_vars[i] == 6, start_day_vars[i] == 7, start_day_vars[i] == 8)))

# Check for solution
if s.check() == sat:
    model = s.model()
    cities_sequence = [model.evaluate(c).as_long() for c in city_vars]
    start_days = [model.evaluate(sd).as_long() for sd in start_day_vars]
    
    # Generate itinerary
    itinerary = {}
    for i in range(8):
        city_code = cities_sequence[i]
        city_name = city_names[city_code]
        start = start_days[i]
        duration = durations[city_code]
        for day in range(start, start + duration):
            itinerary[day] = city_name
    
    # Output JSON
    output = {"itinerary": [{"day": day, "city": itinerary[day]} for day in sorted(itinerary.keys())]}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")