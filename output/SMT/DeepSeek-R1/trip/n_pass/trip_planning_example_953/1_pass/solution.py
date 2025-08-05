import z3
import json

# Map cities to integers and vice versa
cities = {
    'V': 'Venice',
    'A': 'Salzburg',
    'S': 'Stockholm',
    'F': 'Frankfurt',
    'L': 'Florence',
    'B': 'Barcelona',
    'T': 'Stuttgart'
}
city_to_int = {abbr: idx for idx, abbr in enumerate(cities.keys())}
int_to_city = {idx: abbr for abbr, idx in city_to_int.items()}
int_to_fullname = {idx: cities[abbr] for idx, abbr in int_to_city.items()}

# Required days for each city (by integer)
req_days = {
    city_to_int['V']: 5,  # Venice
    city_to_int['A']: 4,  # Salzburg
    city_to_int['S']: 2,  # Stockholm
    city_to_int['F']: 4,  # Frankfurt
    city_to_int['L']: 4,  # Florence
    city_to_int['B']: 2,  # Barcelona
    city_to_int['T']: 3   # Stuttgart
}

# Direct flight edges (as integer pairs)
edges = [
    (city_to_int['B'], city_to_int['F']),
    (city_to_int['L'], city_to_int['F']),
    (city_to_int['S'], city_to_int['B']),
    (city_to_int['B'], city_to_int['L']),
    (city_to_int['V'], city_to_int['B']),
    (city_to_int['T'], city_to_int['B']),
    (city_to_int['F'], city_to_int['A']),
    (city_to_int['S'], city_to_int['F']),
    (city_to_int['T'], city_to_int['S']),
    (city_to_int['T'], city_to_int['F']),
    (city_to_int['V'], city_to_int['T']),
    (city_to_int['V'], city_to_int['F'])
]
# Make the flight graph symmetric
edges_sym = set()
for a, b in edges:
    edges_sym.add((a, b))
    edges_sym.add((b, a))

# Create Z3 variables for the 6 segments (after Venice)
c0, c1, c2, c3, c4, c5 = [z3.Int(f'c{i}') for i in range(6)]
solver = z3.Solver()

# Each segment's city must be one of the non-Venice cities (1 to 6)
non_venice = [1, 2, 3, 4, 5, 6]
for c in [c0, c1, c2, c3, c4, c5]:
    solver.add(z3.Or([c == val for val in non_venice]))

# All cities in the segments must be distinct
solver.add(z3.Distinct(c0, c1, c2, c3, c4, c5))

# Flight constraints: consecutive cities must have a direct flight
# From Venice (0) to the first segment city (c0)
solver.add(z3.Or([z3.And(0 == a, c0 == b) for (a, b) in edges_sym]))
# Between consecutive segments
solver.add(z3.Or([z3.And(c0 == a, c1 == b) for (a, b) in edges_sym]))
solver.add(z3.Or([z3.And(c1 == a, c2 == b) for (a, b) in edges_sym]))
solver.add(z3.Or([z3.And(c2 == a, c3 == b) for (a, b) in edges_sym]))
solver.add(z3.Or([z3.And(c3 == a, c4 == b) for (a, b) in edges_sym]))
solver.add(z3.Or([z3.And(c4 == a, c5 == b) for (a, b) in edges_sym]))

# Check for a solution
if solver.check() == z3.sat:
    model = solver.model()
    c0_val = model[c0].as_long()
    c1_val = model[c1].as_long()
    c2_val = model[c2].as_long()
    c3_val = model[c3].as_long()
    c4_val = model[c4].as_long()
    c5_val = model[c5].as_long()
    
    # Segment cities: Venice (0) followed by the 6 assigned cities
    seg_cities = [0, c0_val, c1_val, c2_val, c3_val, c4_val, c5_val]
    
    # Calculate start and end days for each segment
    starts = [1]  # Venice starts on day 1
    ends = [5]    # Venice ends on day 5
    for i in range(1, 7):
        start_i = ends[i-1]  # start is the end of the previous segment
        dur = req_days[seg_cities[i]]
        end_i = start_i + dur - 1
        starts.append(start_i)
        ends.append(end_i)
    
    # Build itinerary: for each segment, for each day in [start, end], add an entry
    itinerary = []
    for seg_idx in range(7):
        city_int = seg_cities[seg_idx]
        city_abbr = int_to_city[city_int]
        city_name = int_to_fullname[city_int]
        for day in range(starts[seg_idx], ends[seg_idx] + 1):
            itinerary.append({"day": day, "place": city_name})
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")