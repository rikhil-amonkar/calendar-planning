import itertools
import json

# Define input constraints
cities = ['Vilnius', 'Munich', 'Mykonos']
durations = {'Vilnius': 4, 'Munich': 3, 'Mykonos': 7}
flights = {('Vilnius', 'Munich'), ('Munich', 'Vilnius'),
           ('Munich', 'Mykonos'), ('Mykonos', 'Munich')}

# Find valid city sequences with direct flights between consecutive cities
valid_sequences = []
for perm in itertools.permutations(cities):
    valid = True
    for i in range(len(perm) - 1):
        if (perm[i], perm[i+1]) not in flights:
            valid = False
            break
    if valid:
        valid_sequences.append(perm)

# Use the first valid sequence to build the itinerary
sequence = valid_sequences[0]
itinerary = []
current_start = 1

for city in sequence:
    duration = durations[city]
    end_day = current_start + duration - 1
    itinerary.append({
        'day_range': f"Day {current_start}-{end_day}",
        'place': city
    })
    current_start = end_day  # Next city starts on the same day as current city's end

# Output as JSON
result = {'itinerary': itinerary}
print(json.dumps(result, indent=2))