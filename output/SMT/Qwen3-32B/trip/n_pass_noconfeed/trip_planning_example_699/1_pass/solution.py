import z3

# Define cities as an EnumSort
City = z3.DeclareSort('City')
H, D, L, He, M, R = z3.Consts('H D L He M R', City)

# Define the sequence of cities
seq = [z3.Const(f'seq_{i}', City) for i in range(6)]

# Add constraint that all cities are distinct
solver = z3.Solver()
solver.add(z3.Distinct(seq))

# Define start day variables for each city
S_H = z3.Int('S_H')
S_D = z3.Int('S_D')
S_L = z3.Int('S_L')
S_He = z3.Int('S_He')
S_M = z3.Int('S_M')
S_R = z3.Int('S_R')

# Map each city to its start day variable
S = {
    H: S_H,
    D: S_D,
    L: S_L,
    He: S_He,
    M: S_M,
    R: S_R,
}

# Add fixed start days
solver.add(S_H == 1)
solver.add(S_D == 2)
solver.add(S_R == 9)

# Define durations for each city
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
    # Add constraint on start days
    solver.add(S[next_city] == S[prev] + duration[prev] - 1)

# Check if the constraints are satisfiable
if solver.check() == z3.sat:
    model = solver.model()
    # Extract the sequence
    sequence = [model.evaluate(seq[i]) for i in range(6)]
    # Extract the start days
    start_days = {city: model.evaluate(S[city]).as_long() for city in [H, D, L, He, M, R]}
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
        # The 'place' is like 'H', 'D', etc.
        city_code = item["place"]
        item["place"] = city_name_map[city_code]
    # Output as JSON
    import json
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")