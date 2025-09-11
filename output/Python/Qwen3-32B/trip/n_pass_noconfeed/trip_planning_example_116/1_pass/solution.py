import json
from itertools import permutations

# Define trip parameters
cities = ['Split', 'London', 'Santorini']
required_days = {
    'Split': 6,
    'London': 7,
    'Santorini': 7
}
direct_flights = {frozenset(['Split', 'London']), frozenset(['London', 'Santorini'])}
conference_days_santorini = [12, 18]

# Generate valid sequences based on direct flight constraints
valid_sequences = []
for seq in permutations(cities):
    valid = True
    for i in range(len(seq) - 1):
        city_a, city_b = seq[i], seq[i + 1]
        if frozenset([city_a, city_b]) not in direct_flights:
            valid = False
            break
    if valid:
        valid_sequences.append(seq)

# Find the valid itinerary that meets conference constraints
valid_itinerary = None
for sequence in valid_sequences:
    current_day = 1
    itinerary = []
    santorini_days = None
    for city in sequence:
        days_in_city = required_days[city]
        start_day = current_day
        end_day = start_day + days_in_city - 1
        itinerary.append((start_day, end_day, city))
        current_day = end_day  # next city starts on this day
        if city == 'Santorini':
            santorini_days = (start_day, end_day)
    # Check if Santorini includes both conference days
    if santorini_days is not None:
        start_s, end_s = santorini_days
        if (12 >= start_s and 12 <= end_s) and (18 >= start_s and 18 <= end_s):
            valid_itinerary = itinerary
            break

# Generate and print the JSON output
if valid_itinerary:
    json_itinerary = []
    for start, end, place in valid_itinerary:
        day_range = f"Day {start}-{end}"
        json_itinerary.append({"day_range": day_range, "place": place})
    print(json.dumps({"itinerary": json_itinerary}, indent=2))
else:
    print(json.dumps({"error": "No valid itinerary found"}))