import json

city_durations = {
    'Dubrovnik': 4,
    'Split': 3,
    'Milan': 3,
    'Porto': 4,
    'Krakow': 2,
    'Munich': 5
}

direct_flights = {
    'Dubrovnik': ['Munich'],
    'Split': ['Milan', 'Krakow', 'Munich'],
    'Milan': ['Split', 'Porto', 'Krakow', 'Munich'],
    'Porto': ['Munich', 'Milan'],
    'Krakow': ['Munich', 'Split', 'Milan'],
    'Munich': ['Dubrovnik', 'Split', 'Milan', 'Krakow', 'Porto']
}

fixed_cities = [
    {'city': 'Munich', 'start': 4, 'end': 8},
    {'city': 'Krakow', 'start': 8, 'end': 9},
    {'city': 'Milan', 'start': 11, 'end': 13}
]

# Find city before Munich
prev_before_munich = None
for city, dur in city_durations.items():
    if dur == fixed_cities[0]['start'] and city in direct_flights['Munich']:
        prev_before_munich = city
        break

# Find next city after Krakow (fixed_cities[1])
next_after_krakow = None
for city, dur in city_durations.items():
    if city in [fc['city'] for fc in fixed_cities]:
        continue
    start_day = fixed_cities[1]['end']  # 9
    end_day = start_day + dur - 1
    if city in direct_flights['Krakow']:
        next_after_krakow = city
        break

# Find next city after Milan (fixed_cities[2])
next_after_milan = None
for city, dur in city_durations.items():
    if city in [fc['city'] for fc in fixed_cities] or city == next_after_krakow:
        continue
    start_day = fixed_cities[2]['end']  # 13
    end_day = start_day + dur - 1
    if city in direct_flights['Milan']:
        next_after_milan = city
        break

# Now build the itinerary
itinerary = []

# Add city before Munich
dur_prev_before_munich = city_durations[prev_before_munich]
itinerary.append({
    'day_range': f'Day 1-{dur_prev_before_munich}',
    'place': prev_before_munich
})

# Add fixed cities
for fc in fixed_cities:
    itinerary.append({
        'day_range': f'Day {fc["start"]}-{fc["end"]}',
        'place': fc['city']
    })

# Add next after Krakow
dur_next_after_krakow = city_durations[next_after_krakow]
start_day_next_after_krakow = fixed_cities[1]['end']
end_day_next_after_krakow = start_day_next_after_krakow + dur_next_after_krakow - 1
itinerary.append({
    'day_range': f'Day {start_day_next_after_krakow}-{end_day_next_after_krakow}',
    'place': next_after_krakow
})

# Add next after Milan
dur_next_after_milan = city_durations[next_after_milan]
start_day_next_after_milan = fixed_cities[2]['end']
end_day_next_after_milan = start_day_next_after_milan + dur_next_after_milan - 1
itinerary.append({
    'day_range': f'Day {start_day_next_after_milan}-{end_day_next_after_milan}',
    'place': next_after_milan
})

# Output as JSON
print(json.dumps({'itinerary': itinerary}))