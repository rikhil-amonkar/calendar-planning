import itertools
import json

# Define the cities and their durations
durations = {
    'Reykjavik': 7,
    'Riga': 2,
    'Warsaw': 3,
    'Istanbul': 6,
    'Krakow': 7,
}

# Define allowed flights (both directions)
allowed_flights = {
    ('Istanbul', 'Krakow'),
    ('Krakow', 'Istanbul'),
    ('Warsaw', 'Reykjavik'),
    ('Reykjavik', 'Warsaw'),
    ('Istanbul', 'Warsaw'),
    ('Warsaw', 'Istanbul'),
    ('Riga', 'Istanbul'),
    ('Istanbul', 'Riga'),
    ('Krakow', 'Warsaw'),
    ('Warsaw', 'Krakow'),
    ('Riga', 'Warsaw'),
    ('Warsaw', 'Riga'),
}

# Generate all permutations starting with Riga
remaining_cities = ['Reykjavik', 'Istanbul', 'Krakow', 'Warsaw']
found = False
itinerary = []

for perm in itertools.permutations(remaining_cities):
    sequence = ['Riga'] + list(perm)
    # Check if transitions are allowed
    valid = True
    for i in range(len(sequence) - 1):
        a, b = sequence[i], sequence[i+1]
        if (a, b) not in allowed_flights:
            valid = False
            break
    if not valid:
        continue
    
    # Compute start days for each city in the sequence
    start_days = [1]  # Riga starts on day 1
    for i in range(1, len(sequence)):
        prev_city = sequence[i-1]
        start_day_prev = start_days[i-1]
        start_day_current = start_day_prev + durations[prev_city] - 1
        start_days.append(start_day_current)
    
    # Check if Istanbul's start day is <=7
    ist_position = sequence.index('Istanbul')
    if ist_position == -1:
        continue  # Shouldn't happen since all permutations include Istanbul
    start_day_ist = start_days[ist_position]
    if start_day_ist > 7:
        continue
    
    # If we reach here, this sequence is valid
    # Generate the itinerary
    itinerary = []
    for i in range(len(sequence)):
        city = sequence[i]
        start = start_days[i]
        end = start + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
    found = True
    break  # Assuming there's only one valid solution

if found:
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"error": "No valid itinerary found"}))