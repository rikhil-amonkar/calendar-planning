def convert_minutes(minutes):
    hours = minutes // 60
    mins = minutes % 60
    if hours == 0:
        return '9:00'
    else:
        return f"{hours}:{mins:02d}"

locations = {
    'Pacific Heights': {
        'Marina District': 6,
        'The Castro': 16,
        'Richmond District': 12,
        'Alamo Square': 10,
        'Financial District': 13,
        'Presidio': 11,
        'Mission District': 15,
        'Nob Hill': 8,
        'Russian Hill': 7
    },
    'Marina District': {
        'Pacific Heights': 7,
        'The Castro': 22,
        'Richmond District': 11,
        'Alamo Square': 15,
        'Financial District': 17,
        'Presidio': 10,
        'Mission District': 20,
        'Nob Hill': 12,
        'Russian Hill': 8
    },
    'The Castro': {
        'Pacific Heights': 16,
        'Marina District': 21,
        'Richmond District': 16,
        'Alamo Square': 8,
        'Financial District': 21,
        'Presidio': 20,
        'Mission District': 7,
        'Nob Hill': 16,
        'Russian Hill': 18
    },
    'Richmond District': {
        'Pacific Heights': 10,
        'Marina District': 9,
        'The Castro': 16,
        'Alamo Square': 13,
        'Financial District': 22,
        'Presidio': 7,
        'Mission District': 20,
        'Nob Hill': 17,
        'Russian Hill': 13
    },
    'Alamo Square': {
        'Pacific Heights': 10,
        'Marina District': 15,
        'The Castro': 8,
        'Richmond District': 11,
        'Financial District': 17,
        'Presidio': 17,
        'Mission District': 10,
        'Nob Hill': 11,
        'Russian Hill': 13
    },
    'Financial District': {
        'Pacific Heights': 13,
        'Marina District': 15,
        'The Castro': 20,
        'Richmond District': 21,
        'Alamo Square': 17,
        'Presidio': 22,
        'Mission District': 17,
        'Nob Hill': 8,
        'Russian Hill': 11
    },
    'Presidio': {
        'Pacific Heights': 11,
        'Marina District': 11,
        'The Castro': 21,
        'Richmond District': 7,
        'Alamo Square': 19,
        'Financial District': 23,
        'Mission District': 26,
        'Nob Hill': 18,
        'Russian Hill': 14
    },
    'Mission District': {
        'Pacific Heights': 16,
        'Marina District': 19,
        'The Castro': 7,
        'Richmond District': 20,
        'Alamo Square': 11,
        'Financial District': 15,
        'Presidio': 25,
        'Nob Hill': 12,
        'Russian Hill': 15
    },
    'Nob Hill': {
        'Pacific Heights': 8,
        'Marina District': 12,
        'The Castro': 17,
        'Richmond District': 14,
        'Alamo Square': 11,
        'Financial District': 9,
        'Presidio': 17,
        'Mission District': 13,
        'Russian Hill': 5
    },
    'Russian Hill': {
        'Pacific Heights': 7,
        'Marina District': 7,
        'The Castro': 21,
        'Richmond District': 14,
        'Alamo Square': 15,
        'Financial District': 11,
        'Presidio': 14,
        'Mission District': 16,
        'Nob Hill': 5
    }
}

people = [
    {'name': 'Linda', 'location': 'Marina District', 'start': 1080, 'end': 1260, 'min': 30},
    {'name': 'Kenneth', 'location': 'The Castro', 'start': 570, 'end': 780, 'min': 30},
    {'name': 'Kimberly', 'location': 'Richmond District', 'start': 570, 'end': 1260, 'min': 30},
    {'name': 'Paul', 'location': 'Alamo Square', 'start': 1080, 'end': 1140, 'min': 15},
    {'name': 'Carol', 'location': 'Financial District', 'start': 90, 'end': 720, 'min': 60},
    {'name': 'Brian', 'location': 'Presidio', 'start': 90, 'end': 1260, 'min': 75},
    {'name': 'Laura', 'location': 'Mission District', 'start': 690, 'end': 990, 'min': 30},
    {'name': 'Sandra', 'location': 'Nob Hill', 'start': 90, 'end': 780, 'min': 60},
    {'name': 'Karen', 'location': 'Russian Hill', 'start': 1080, 'end': 1260, 'min': 75}
]

people_sorted = sorted(people, key=lambda x: (x['end'] - x['min']))

current_time = 0
current_location = 'Pacific Heights'
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