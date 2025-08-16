import z3

# Cities and their indices
CITIES = ["Venice", "Salzburg", "Stockholm", "Frankfurt", "Florence", "Barcelona", "Stuttgart"]
CITY_INDEX = {city: idx for idx, city in enumerate(CITIES)}

# Direct flights between cities (bidirectional)
DIRECT_FLIGHTS = set([
    (0, 5), (5, 0),  # Venice - Barcelona
    (0, 6), (6, 0),  # Venice - Stuttgart
    (0, 3), (3, 0),  # Venice - Frankfurt
    (5, 3), (3, 5),  # Barcelona - Frankfurt
    (5, 4), (4, 5),  # Barcelona - Florence
    (5, 2), (2, 5),  # Barcelona - Stockholm
    (5, 6), (6, 5),  # Barcelona - Stuttgart
    (3, 1), (1, 3),  # Frankfurt - Salzburg
    (3, 2), (2, 3),  # Frankfurt - Stockholm
    (3, 6), (6, 3),  # Frankfurt - Stuttgart
    (2, 6), (6, 2),  # Stockholm - Stuttgart
    (4, 3), (3, 4),  # Florence - Frankfurt
])

# Required number of days in each city
DURATIONS = {
    "Venice": 5,
    "Salzburg": 4,
    "Stockholm": 2,
    "Frankfurt": 4,
    "Florence": 4,
    "Barcelona": 2,
    "Stuttgart": 3,
}

# Z3 Solver Setup
solver = z3.Solver()

# Sequence of cities (7 cities total)
sequence = [z3.Int(f"city_{i}") for i in range(7)]

# Constraint 1: First city must be Venice
solver.add(sequence[0] == 0)

# Constraint 2: All cities must be visited exactly once
solver.add(z3.Distinct(sequence))

# Constraint 3: Each city must be a valid index (0-6)
for city in sequence:
    solver.add(z3.And(city >= 0, city <= 6))

# Constraint 4: Consecutive cities must have a direct flight
for i in range(6):
    a, b = sequence[i], sequence[i+1]
    solver.add(z3.Or([z3.And(a == u, b == v) for u, v in DIRECT_FLIGHTS]))

# Solve the problem
if solver.check() == z3.sat:
    model = solver.model()
    seq = [model.eval(city).as_long() for city in sequence]
    city_names = [CITIES[seq[i]] for i in range(7)]

    # Calculate start days for each city
    start_days = [1]  # First city starts on day 1
    for i in range(1, 7):
        prev_duration = DURATIONS[CITIES[seq[i-1]]]
        start_days.append(start_days[i-1] + prev_duration)

    # Generate itinerary
    itinerary = []
    for day in range(1, 19):
        for i in range(7):
            start = start_days[i]
            end = start_days[i] + DURATIONS[city_names[i]] - 1
            if start <= day <= end:
                itinerary.append({"day": day, "city": city_names[i]})
                break

    # Output as JSON
    import json
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No valid itinerary found.")