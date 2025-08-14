import json
from itertools import permutations

required_days = {
    'Prague': 2,
    'Helsinki': 4,
    'Frankfurt': 3,
    'Lyon': 3,
    'Naples': 4
}

allowed_flights = set()
original_flights = [
    ('Prague', 'Lyon'),
    ('Prague', 'Frankfurt'),
    ('Frankfurt', 'Lyon'),
    ('Helsinki', 'Naples'),
    ('Helsinki', 'Frankfurt'),
    ('Naples', 'Frankfurt'),
    ('Prague', 'Helsinki'),
]
for a, b in original_flights:
    allowed_flights.add((a, b))
    allowed_flights.add((b, a))

# Initial order based on constraints
initial_order = ['Prague', 'Helsinki']
remaining_cities = ['Frankfurt', 'Lyon', 'Naples']

# Find valid permutation of remaining cities
valid_order = None
for perm in permutations(remaining_cities):
    candidate = initial_order + list(perm)
    valid = True
    for i in range(len(candidate) - 1):
        if (candidate[i], candidate[i+1]) not in allowed_flights:
            valid = False
            break
    if valid:
        valid_order = candidate
        break

if valid_order:
    # Compute the itinerary day ranges
    itinerary = []
    current_start = 1
    for city in valid_order:
        days = required_days[city]
        end_day = current_start + days - 1
        itinerary.append({
            'day_range': f"Day {current_start}-{end_day}",
            'place': city
        })
        current_start = end_day  # Next city starts on this day

    # Output JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print(json.dumps({"error": "No valid itinerary found"}))