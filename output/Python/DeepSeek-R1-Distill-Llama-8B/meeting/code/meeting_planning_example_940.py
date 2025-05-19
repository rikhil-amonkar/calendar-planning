def convert_minutes(minutes):
    hours = minutes // 60
    mins = minutes % 60
    if hours == 0:
        return '9:00'
    else:
        return f"{hours}:{mins:02d}"

locations = {
    'Union Square': {
        'Mission District': 14,
        'Fisherman's Wharf': 15,
        'Russian Hill': 13,
        'Marina District': 18,
        'North Beach': 10,
        'Chinatown': 7,
        'Pacific Heights': 15,
        'The Castro': 17,
        'Nob Hill': 9,
        'Sunset District': 27
    },
    'Mission District': {
        'Union Square': 15,
        'Fisherman's Wharf': 22,
        'Russian Hill': 15,
        'Marina District': 19,
        'North Beach': 17,
        'Chinatown': 16,
        'Pacific Heights': 16,
        'The Castro': 7,
        'Nob Hill': 12,
        'Sunset District': 24
    },
    'Fisherman's Wharf': {
        'Union Square': 13,
        'Mission District': 22,
        'Russian Hill': 7,
        'Marina District': 9,
        'North Beach': 6,
        'Chinatown': 12,
        'Pacific Heights': 12,
        'The Castro': 27,
        'Nob Hill': 11,
        'Sunset District': 27
    },
    'Russian Hill': {
        'Union Square': 10,
        'Mission District': 16,
        'Fisherman's Wharf': 7,
        'Marina District': 7,
        'North Beach': 5,
        'Chinatown': 9,
        'Pacific Heights': 7,
        'The Castro': 21,
        'Nob Hill': 5,
        'Sunset District': 23
    },
    'Marina District': {
        'Union Square': 16,
        'Mission District': 20,
        'Fisherman's Wharf': 10,
        'Russian Hill': 8,
        'North Beach': 11,
        'Chinatown': 15,
        'Pacific Heights': 7,
        'The Castro': 22,
        'Nob Hill': 12,
        'Sunset District': 19
    },
    'North Beach': {
        'Union Square': 7,
        'Mission District': 18,
        'Fisherman's Wharf': 5,
        'Russian Hill': 4,
        'Marina District': 9,
        'Chinatown': 6,
        'Pacific Heights': 8,
        'The Castro': 23,
        'Nob Hill': 7,
        'Sunset District': 27
    },
    'Chinatown': {
        'Union Square': 7,
        'Mission District': 17,
        'Fisherman's Wharf': 8,
        'Russian Hill': 7,
        'Marina District': 12,
        'North Beach': 3,
        'Pacific Heights': 10,
        'The Castro': 22,
        'Nob Hill': 9,
        'Sunset District': 29
    },
    'Pacific Heights': {
        'Union Square': 12,
        'Mission District': 15,
        'Fisherman's Wharf': 13,
        'Russian Hill': 7,
        'Marina District': 6,
        'North Beach': 9,
        'Chinatown': 11,
        'The Castro': 16,
        'Nob Hill': 8,
        'Sunset District': 21
    },
    'The Castro': {
        'Union Square': 19,
        'Mission District': 7,
        'Fisherman's Wharf': 24,
        'Russian Hill': 18,
        'Marina District': 21,
        'North Beach': 20,
        'Chinatown': 22,
        'Pacific Heights': 16,
        'Nob Hill': 16,
        'Sunset District': 17
    },
    'Nob Hill': {
        'Union Square': 7,
        'Mission District': 13,
        'Fisherman's Wharf': 10,
        'Russian Hill': 5,
        'Marina District': 11,
        'North Beach': 8,
        'Chinatown': 6,
        'Pacific Heights': 8,
        'The Castro': 17,
        'Sunset District': 24
    },
    'Sunset District': {
        'Union Square': 30,
        'Mission District': 25,
        'Fisherman's Wharf': 29,
        'Russian Hill': 24,
        'Marina District': 21,
        'North Beach': 28,
        'Chinatown': 30,
        'Pacific Heights': 21,
        'The Castro': 17,
        'Nob Hill': 27
    }
}

people = [
    {'name': 'Kevin', 'location': 'Mission District', 'start': 1080, 'end': 1260, 'min': 60},
    {'name': 'Mark', 'location': 'Fisherman's Wharf', 'start': 300, 'end': 720, 'min': 90},
    {'name': 'Jessica', 'location': 'Russian Hill', 'start': 0, 'end': 540, 'min': 120},
    {'name': 'Jason', 'location': 'Marina District', 'start': 615, 'end': 1260, 'min': 120},
    {'name': 'John', 'location': 'North Beach', 'start': 90, 'end': 360, 'min': 15},
    {'name': 'Karen', 'location': 'Chinatown', 'start': 495, 'end': 630, 'min': 75},
    {'name': 'Sarah', 'location': 'Pacific Heights', 'start': 570, 'end': 615, 'min': 45},
    {'name': 'Amanda', 'location': 'The Castro', 'start': 1080, 'end': 1140, 'min': 60},
    {'name': 'Nancy', 'location': 'Nob Hill', 'start': 90, 'end': 210, 'min': 45},
    {'name': 'Rebecca', 'location': 'Sunset District', 'start': 540, 'end': 1080, 'min': 75}
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