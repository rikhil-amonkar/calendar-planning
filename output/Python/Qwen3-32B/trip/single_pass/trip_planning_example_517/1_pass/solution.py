import itertools
import json

# Define input parameters
cities = ['Bucharest', 'Warsaw', 'Stuttgart', 'Copenhagen', 'Dubrovnik']
durations = {
    'Bucharest': 6,
    'Warsaw': 2,
    'Stuttgart': 7,
    'Copenhagen': 3,
    'Dubrovnik': 5
}
flight_connections = {
    ('Warsaw', 'Copenhagen'),
    ('Copenhagen', 'Warsaw'),
    ('Stuttgart', 'Copenhagen'),
    ('Copenhagen', 'Stuttgart'),
    ('Warsaw', 'Stuttgart'),
    ('Stuttgart', 'Warsaw'),
    ('Bucharest', 'Copenhagen'),
    ('Copenhagen', 'Bucharest'),
    ('Bucharest', 'Warsaw'),
    ('Warsaw', 'Bucharest'),
    ('Copenhagen', 'Dubrovnik'),
    ('Dubrovnik', 'Copenhagen'),
}

# Find valid permutations
for perm in itertools.permutations(cities):
    # Check if all consecutive transitions are valid
    valid = True
    for i in range(len(perm) - 1):
        if (perm[i], perm[i+1]) not in flight_connections:
            valid = False
            break
    if not valid:
        continue

    # Compute day ranges
    day_ranges = []
    current_day = 1
    for city in perm:
        dur = durations[city]
        end_day = current_day + dur - 1
        day_ranges.append((current_day, end_day, city))
        current_day = end_day

    # Check constraints:
    # 1. Bucharest is first and has 1-6
    if day_ranges[0][0] != 1 or day_ranges[0][1] != 6 or day_ranges[0][2] != 'Bucharest':
        continue

    # 2. Stuttgart's days are 7-13
    stuttgart_entry = None
    for entry in day_ranges:
        if entry[2] == 'Stuttgart':
            stuttgart_entry = entry
            break
    if stuttgart_entry is None:
        continue
    if stuttgart_entry[0] != 7 or stuttgart_entry[1] != 13:
        continue

    # If all constraints are met, build the itinerary
    itinerary = []
    for start, end, city in day_ranges:
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})

    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
    exit()

# If no valid itinerary found
print(json.dumps({"error": "No valid itinerary found"}, indent=2))