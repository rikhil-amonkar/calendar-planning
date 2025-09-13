import z3

# Define cities as an EnumSort
City = z3.DeclareSort('City')
H, D, L, He, M, R = z3.Consts('H D L He M R', City)

# Define the sequence of cities
seq = [z3.Const(f'seq_{i}', City) for i in range(6)]

# Add constraint that all cities are distinct
solver = z3.Solver()
solver.add(z3.Distinct(seq))

# Define S as a function from City to Int
S_func = z3.Function('S', City, z3.IntSort())

# Add fixed start days
solver.add(S_func(H) == 1)
solver.add(S_func(D) == 2)
solver.add(S_func(R) == 9)

# Define durations for each city (used in itinerary generation)
duration = {
    H: 2,
    D: 5,
    L: 5,
    He: 4,
    M: 3,
    R: 2,
}

# Define allowed direct flights
allowed_flights = [
    (H, D), (D, H),
    (H, L), (L, H),
    (D, He), (He, D),
    (He, R), (R, He),
    (D, L), (L, D),
    (D, R), (R, D),
    (R, L), (L, R),
    (L, M), (M, L),
    (H, He), (He, H),
    (He, L), (L, He),
]

# For each consecutive pair in the sequence, add constraints
for i in range(5):
    prev = seq[i]
    next_city = seq[i+1]
    # Add constraint that the transition is allowed
    allowed = z3.Or([z3.And(prev == p, next_city == n) for p, n in allowed_flights])
    solver.add(allowed)
    # Compute duration_prev based on prev
    duration_prev = z3.If(prev == H, 2,
                   z3.If(prev == D, 5,
                   z3.If(prev == L, 5,
                   z3.If(prev == He, 4,
                   z3.If(prev == M, 3,
                         2)))))
    # Add constraint on start days
    solver.add(S_func(next_city) == S_func(prev) + duration_prev - 1)

# Check if the constraints are satisfiable
if solver.check() == z3.sat:
    model = solver.model()
    # Extract the sequence
    sequence = [model.evaluate(seq[i]) for i in range(6)]
    # Extract the start days
    start_days = {city: model.evaluate(S_func(city)).as_long() for city in [H, D, L, He, M, R]}
    # Generate the itinerary
    itinerary = []
    for city in sequence:
        start = start_days[city]
        end = start + duration[city] - 1
        day_range = f"Day {start}-Day {end}"
        itinerary.append({"day_range": day_range, "place": str(city)})
    # Convert city names to the actual city names
    city_name_map = {
        'H': "Hamburg",
        'D': "Dublin",
        'L': "London",
        'He': "Helsinki",
        'M': "Mykonos",
        'R': "Reykjavik",
    }
    for item in itinerary:
        city_code = item["place"]
        item["place"] = city_name_map[city_code]
    # Output as JSON
    import json
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")