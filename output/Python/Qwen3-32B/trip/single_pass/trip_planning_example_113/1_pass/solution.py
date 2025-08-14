import itertools
import json

# Define the adjacency list for direct flights
adj = {
    'Naples': ['Milan'],
    'Milan': ['Naples', 'Seville'],
    'Seville': ['Milan']
}

# Required days in each city
required_days = {
    'Naples': 3,
    'Milan': 7,
    'Seville': 4
}

# List of cities to visit
cities = ['Naples', 'Milan', 'Seville']

# Generate all valid sequences of cities based on direct flights
valid_sequences = []
for seq in itertools.permutations(cities):
    valid = True
    for i in range(1, len(seq)):
        prev_city = seq[i-1]
        current_city = seq[i]
        if current_city not in adj[prev_city]:
            valid = False
            break
    if valid:
        valid_sequences.append(seq)

# Find the valid sequence that satisfies the Seville show constraint
itinerary_plan = None
for seq in valid_sequences:
    current_start = 1
    seville_start = None
    seville_end = None
    plan = []
    for city in seq:
        days = required_days[city]
        end = current_start + days - 1
        plan.append((current_start, end, city))
        if city == 'Seville':
            seville_start = current_start
            seville_end = end
        current_start = end
    # Check if Seville stay includes days 9-12
    if seville_start is not None and seville_start <= 9 and seville_end >= 12:
        itinerary_plan = plan
        break

# Generate the JSON output
itinerary = []
for start, end, city in itinerary_plan:
    itinerary.append({
        'day_range': f"Day {start}-{end}",
        'place': city
    })

print(json.dumps({"itinerary": itinerary}))