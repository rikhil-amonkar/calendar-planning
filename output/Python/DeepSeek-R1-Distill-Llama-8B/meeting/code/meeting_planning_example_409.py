def convert_minutes(minutes):
    hours = minutes // 60
    mins = minutes % 60
    if hours == 0:
        return '9:00'
    else:
        return f"{hours}:{mins:02d}"

locations = {
    'Fisherman's Wharf': {
        'Bayview': 26,
        'Golden Gate Park': 25,
        'Nob Hill': 11,
        'Marina District': 9,
        'Embarcadero': 8
    },
    'Bayview': {
        'Fisherman's Wharf': 25,
        'Golden Gate Park': 22,
        'Nob Hill': 20,
        'Marina District': 25,
        'Embarcadero': 19
    },
    'Golden Gate Park': {
        'Fisherman's Wharf': 24,
        'Bayview': 23,
        'Nob Hill': 20,
        'Marina District': 16,
        'Embarcadero': 25
    },
    'Nob Hill': {
        'Fisherman's Wharf': 11,
        'Bayview': 19,
        'Golden Gate Park': 17,
        'Marina District': 11,
        'Embarcadero': 9
    },
    'Marina District': {
        'Fisherman's Wharf': 10,
        'Bayview': 27,
        'Golden Gate Park': 18,
        'Nob Hill': 12,
        'Embarcadero': 14
    },
    'Embarcadero': {
        'Fisherman's Wharf': 6,
        'Bayview': 21,
        'Golden Gate Park': 25,
        'Nob Hill': 10,
        'Marina District': 12
    }
}

people = [
    {'name': 'Thomas', 'location': 'Bayview', 'start': 630, 'end': 990, 'min': 120},
    {'name': 'Stephanie', 'location': 'Golden Gate Park', 'start': 690, 'end': 1140, 'min': 30},
    {'name': 'Laura', 'location': 'Nob Hill', 'start': 90, 'end': 480, 'min': 30},
    {'name': 'Betty', 'location': 'Marina District', 'start': 690, 'end': 1260, 'min': 45},
    {'name': 'Patricia', 'location': 'Embarcadero', 'start': 330, 'end': 1260, 'min': 45}
]

people_sorted = sorted(people, key=lambda x: (x['end'] - x['min']))

current_time = 0
current_location = 'Fisherman's Wharf'
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