import itertools
import json

# Define the cities and their required stay durations
required_days = {
    'Warsaw': 2,
    'Budapest': 7,
    'Paris': 4,
    'Riga': 7
}

# Define direct flight connections (bidirectional)
direct_flights = {
    ('Warsaw', 'Budapest'),
    ('Warsaw', 'Riga'),
    ('Budapest', 'Paris'),
    ('Warsaw', 'Paris'),
    ('Paris', 'Riga'),
    # Add reverse directions
    ('Budapest', 'Warsaw'),
    ('Riga', 'Warsaw'),
    ('Paris', 'Budapest'),
    ('Paris', 'Warsaw'),
    ('Riga', 'Paris'),
}

# Generate permutations of cities after Warsaw
remaining_cities = ['Budapest', 'Paris', 'Riga']
valid_itinerary = None

for perm in itertools.permutations(remaining_cities):
    order = ['Warsaw'] + list(perm)
    # Check if all transitions are valid
    valid_transitions = True
    for i in range(len(order) - 1):
        current, next_city = order[i], order[i + 1]
        if (current, next_city) not in direct_flights:
            valid_transitions = False
            break
    if not valid_transitions:
        continue

    # Calculate day ranges
    itinerary_days = []
    current_start = 1
    for city in order:
        days_needed = required_days[city]
        end_day = current_start + days_needed - 1
        itinerary_days.append((current_start, end_day, city))
        current_start = end_day

    # Check Riga's start day is 11
    riga_start = None
    for start, end, city in itinerary_days:
        if city == 'Riga':
            riga_start = start
            break
    if riga_start != 11:
        continue

    # Check Warsaw's days
    warsaw_start, warsaw_end, _ = itinerary_days[0]
    if warsaw_start != 1 or warsaw_end != 2:
        continue

    valid_itinerary = itinerary_days
    break

# Convert to JSON format
itinerary_list = []
for start, end, city in valid_itinerary:
    day_range = f"Day {start}-{end}"
    itinerary_list.append({"day_range": day_range, "place": city})

result = {"itinerary": itinerary_list}
print(json.dumps(result, indent=2))