import itertools
import json

# Define direct flights (both directions)
direct_flights = {
    ('Paris', 'Bucharest'), ('Bucharest', 'Paris'),
    ('Seville', 'Paris'), ('Paris', 'Seville'),
    ('Madrid', 'Bucharest'), ('Bucharest', 'Madrid'),
    ('Madrid', 'Paris'), ('Paris', 'Madrid'),
    ('Madrid', 'Seville'), ('Seville', 'Madrid'),
}

# Cities and their required durations
durations = {
    'Madrid': 7,
    'Seville': 3,
    'Paris': 6,
    'Bucharest': 2
}

# Generate possible sequences: first is Madrid, last is Bucharest
middle_cities = ['Seville', 'Paris']
valid_sequences = []

for perm in itertools.permutations(middle_cities):
    sequence = ['Madrid'] + list(perm) + ['Bucharest']
    valid = True
    for i in range(len(sequence) - 1):
        a, b = sequence[i], sequence[i+1]
        if (a, b) not in direct_flights:
            valid = False
            break
    if valid:
        valid_sequences.append(sequence)

# Compute itinerary for the first valid sequence
itinerary = []
current_day = 1
for city in valid_sequences[0]:
    duration = durations[city]
    end_day = current_day + duration - 1
    day_range = f"Day {current_day}-{end_day}"
    itinerary.append({"day_range": day_range, "place": city})
    current_day = end_day

# Output as JSON
print(json.dumps({"itinerary": itinerary}))