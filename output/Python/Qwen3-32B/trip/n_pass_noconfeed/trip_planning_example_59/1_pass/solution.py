import json

# Define trip constraints
durations = {
    'Lyon': 7,
    'Bucharest': 7,
    'Porto': 4
}

# Valid sequences based on direct flight connections
valid_sequences = [
    ['Bucharest', 'Lyon', 'Porto'],
    ['Porto', 'Lyon', 'Bucharest']
]

# Find the sequence that satisfies the wedding constraint
selected_sequence = None
for sequence in valid_sequences:
    current_start = 1
    bucharest_start = None
    for city in sequence:
        duration = durations[city]
        if city == 'Bucharest':
            bucharest_start = current_start
        end_day = current_start + duration - 1
        current_start = end_day
    if bucharest_start is not None and bucharest_start <= 7:
        selected_sequence = sequence
        break

# Generate itinerary from selected sequence
itinerary = []
current_start = 1
for city in selected_sequence:
    duration = durations[city]
    end_day = current_start + duration - 1
    day_range = f"Day {current_start}-{end_day}"
    itinerary.append({"day_range": day_range, "place": city})
    current_start = end_day

# Output JSON
print(json.dumps({"itinerary": itinerary}))