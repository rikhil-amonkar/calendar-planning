def convert_minutes(minutes):
    hours = minutes // 60
    mins = minutes % 60
    if hours == 0:
        return '9:00'
    else:
        return f"{hours}:{mins:02d}"

locations = {
    'Union Square': {
        'Nob Hill': 9,
        'Haight-Ashbury': 18,
        'Chinatown': 7,
        'Marina District': 18
    },
    'Nob Hill': {
        'Union Square': 7,
        'Haight-Ashbury': 13,
        'Chinatown': 6,
        'Marina District': 11
    },
    'Haight-Ashbury': {
        'Union Square': 17,
        'Nob Hill': 15,
        'Chinatown': 19,
        'Marina District': 17
    },
    'Chinatown': {
        'Union Square': 7,
        'Nob Hill': 8,
        'Haight-Ashbury': 19,
        'Marina District': 12
    },
    'Marina District': {
        'Union Square': 16,
        'Nob Hill': 12,
        'Haight-Ashbury': 16,
        'Chinatown': 16
    }
}

people = [
    {'name': 'Karen', 'location': 'Nob Hill', 'start': 990, 'end': 1260, 'min': 30},
    {'name': 'Joseph', 'location': 'Haight-Ashbury', 'start': 570, 'end': 990, 'min': 90},
    {'name': 'Sandra', 'location': 'Chinatown', 'start': 0, 'end': 990, 'min': 75},
    {'name': 'Nancy', 'location': 'Marina District', 'start': 330, 'end': 1260, 'min': 105}
]

people_sorted = sorted(people, key=lambda x: (x['end'] - x['min']))

current_time = 0
current_location = 'Union Square'
itinerary = []

for person in people_sorted:
    location = person['location']
    travel_time = locations[current_location][location]
    arrival_time = current_time + travel_time
    latest_start = person['end'] - person['min']
    if arrival_time <= latest_start:
        meeting_end = arrival_time + person['min']
        start_str = convert_minutes(arrival_time)
        end_str = convert_minutes(meeting_end)
        itinerary.append({
            'action': 'meet',
            'location': location,
            'person': person['name'],
            'start_time': start_str,
            'end_time': end_str
        })
        current_time = meeting_end
        current_location = location

print(json.dumps(itinerary))