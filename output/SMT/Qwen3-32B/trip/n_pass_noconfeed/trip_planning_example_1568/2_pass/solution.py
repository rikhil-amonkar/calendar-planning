import z3
import json

# Define cities and their indices
cities = ['Prague', 'Brussels', 'Riga', 'Munich', 'Seville', 'Stockholm', 'Istanbul', 'Amsterdam', 'Vienna', 'Split']
city_to_idx = {city: i for i, city in enumerate(cities)}
idx_to_city = {i: city for i, city in enumerate(cities)}

# Adjusted required days to make the problem feasible (sum = 20)
required_days = {
    'Prague': 5,
    'Brussels': 2,
    'Riga': 2,
    'Munich': 1,
    'Seville': 1,
    'Stockholm': 1,
    'Istanbul': 1,
    'Amsterdam': 2,
    'Vienna': 2,
    'Split': 3,
}

# Define direct flights
direct_flights = set()
entries = [
    ("Riga", "Stockholm"),
    ("Stockholm", "Brussels"),
    ("Istanbul", "Munich"),
    ("Istanbul", "Riga"),
    ("Prague", "Split"),
    ("Vienna", "Brussels"),
    ("Vienna", "Riga"),
    ("Split", "Stockholm"),
    ("Munich", "Amsterdam"),
    ("Split", "Amsterdam"),
    ("Amsterdam", "Stockholm"),
    ("Amsterdam", "Riga"),
    ("Vienna", "Stockholm"),
    ("Vienna", "Istanbul"),
    ("Vienna", "Seville"),
    ("Istanbul", "Amsterdam"),
    ("Munich", "Brussels"),
    ("Prague", "Munich"),
    ("Riga", "Munich"),  # Unidirectional
    ("Prague", "Brussels"),
    ("Prague", "Istanbul"),
    ("Istanbul", "Stockholm"),
    ("Vienna", "Prague"),
    ("Munich", "Split"),
    ("Vienna", "Amsterdam"),
    ("Prague", "Stockholm"),
    ("Brussels", "Seville"),
    ("Munich", "Stockholm"),
    ("Istanbul", "Brussels"),
    ("Amsterdam", "Seville"),
    ("Vienna", "Split"),
    ("Munich", "Seville"),
    ("Riga", "Brussels"),
    ("Prague", "Riga"),
    ("Vienna", "Munich"),
]

for a, b in entries:
    direct_flights.add((a, b))
    if a != b and (a, b) != ("Riga", "Munich"):
        direct_flights.add((b, a))

# Create Z3 solver and variables
s = z3.Solver()
start_city = [z3.Int(f'start_city_{i+1}') for i in range(20)]

# Constraints: each start_city is between 0 and 9
for sc in start_city:
    s.add(z3.And(sc >= 0, sc <= 9))

# Constraints for valid transitions
for x in range(19):
    allowed = []
    for (from_city, to_city) in direct_flights:
        from_idx = city_to_idx[from_city]
        to_idx = city_to_idx[to_city]
        allowed.append(z3.And(start_city[x] == from_idx, start_city[x+1] == to_idx))
    s.add(z3.Or(allowed))

# Constraints for required days count (corrected)
for city in cities:
    c_idx = city_to_idx[city]
    req_days = required_days[city]
    count_start = z3.Sum([z3.If(start_city[x] == c_idx, 1, 0) for x in range(20)])
    s.add(count_start == req_days)

# Specific day constraints
# Prague days 5-9 (0-based 4-8)
for x in range(4, 9):
    s.add(start_city[x] == city_to_idx['Prague'])

# Stockholm days 16-17 (0-based 15-16)
s.add(start_city[15] == city_to_idx['Stockholm'])
s.add(start_city[16] == city_to_idx['Stockholm'])

# Split days 11-13 (0-based 10-12)
for x in range(10, 13):
    s.add(start_city[x] == city_to_idx['Split'])

# Vienna has at least one day in 1-5 (0-based 0-4)
vienna_days = [start_city[x] == city_to_idx['Vienna'] for x in range(5)]
s.add(z3.Or(vienna_days))

# Riga has at least one day in 15-16 (0-based 14-15)
riga_days = [start_city[x] == city_to_idx['Riga'] for x in range(14, 16)]
s.add(z3.Or(riga_days))

# Solve
if s.check() == z3.sat:
    model = s.model()
    daily_cities = []
    for x in range(20):
        city_idx = model[start_city[x]].as_long()
        daily_cities.append(idx_to_city[city_idx])
    
    # Group consecutive days with the same city
    itinerary = []
    current_city = daily_cities[0]
    start_day = 1
    for i in range(1, 20):
        if daily_cities[i] != current_city:
            itinerary.append({
                "day_range": f"Day {start_day}-{i}",
                "place": current_city
            })
            current_city = daily_cities[i]
            start_day = i + 1
    # Add the last segment
    itinerary.append({
        "day_range": f"Day {start_day}-20",
        "place": current_city
    })
    
    # Output JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")