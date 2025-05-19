def convert_minutes(minutes):
    hours = minutes // 60
    mins = minutes % 60
    if hours == 0:
        return '9:00'
    else:
        return f"{hours}:{mins:02d}"

locations = {
    'Bayview': {
        'North Beach': 22,
        'Fisherman's Wharf': 25,
        'Haight-Ashbury': 19,
        'Nob Hill': 20,
        'Golden Gate Park': 22,
        'Union Square': 18,
        'Alamo Square': 16,
        'Presidio': 32,
        'Chinatown': 19,
        'Pacific Heights': 23
    },
    'North Beach': {
        'Bayview': 25,
        'Fisherman's Wharf': 5,
        'Haight-Ashbury': 18,
        'Nob Hill': 7,
        'Golden Gate Park': 22,
        'Union Square': 7,
        'Alamo Square': 16,
        'Presidio': 17,
        'Chinatown': 6,
        'Pacific Heights': 8
    },
    'Fisherman's Wharf': {
        'Bayview': 26,
        'North Beach': 6,
        'Haight-Ashbury': 22,
        'Nob Hill': 11,
        'Golden Gate Park': 25,
        'Union Square': 13,
        'Alamo Square': 21,
        'Presidio': 17,
        'Chinatown': 12,
        'Pacific Heights': 12
    },
    'Haight-Ashbury': {
        'Bayview': 18,
        'North Beach': 19,
        'Fisherman's Wharf': 23,
        'Nob Hill': 15,
        'Golden Gate Park': 7,
        'Union Square': 19,
        'Alamo Square': 5,
        'Presidio': 15,
        'Chinatown': 19,
        'Pacific Heights': 12
    },
    'Nob Hill': {
        'Bayview': 19,
        'North Beach': 8,
        'Fisherman's Wharf': 10,
        'Haight-Ashbury': 13,
        'Golden Gate Park': 17,
        'Union Square': 7,
        'Alamo Square': 11,
        'Presidio': 17,
        'Chinatown': 6,
        'Pacific Heights': 8
    },
    'Golden Gate Park': {
        'Bayview': 23,
        'North Beach': 23,
        'Fisherman's Wharf': 24,
        'Haight-Ashbury': 7,
        'Nob Hill': 20,
        'Union Square': 22,
        'Alamo Square': 9,
        'Presidio': 11,
        'Chinatown': 23,
        'Pacific Heights': 16
    },
    'Union Square': {
        'Bayview': 15,
        'North Beach': 10,
        'Fisherman's Wharf': 15,
        'Haight-Ashbury': 18,
        'Nob Hill': 9,
        'Golden Gate Park': 22,
        'Alamo Square': 15,
        'Presidio': 24,
        'Chinatown': 7,
        'Pacific Heights': 15
    },
    'Alamo Square': {
        'Bayview': 16,
        'North Beach': 15,
        'Fisherman's Wharf': 19,
        'Haight-Ashbury': 5,
        'Nob Hill': 11,
        'Golden Gate Park': 9,
        'Union Square': 14,
        'Presidio': 17,
        'Chinatown': 15,
        'Pacific Heights': 10
    },
    'Presidio': {
        'Bayview': 31,
        'North Beach': 18,
        'Fisherman's Wharf': 19,
        'Haight-Ashbury': 15,
        'Nob Hill': 18,
        'Golden Gate Park': 12,
        'Union Square': 22,
        'Alamo Square': 19,
        'Chinatown': 21,
        'Pacific Heights': 11
    },
    'Chinatown': {
        'Bayview': 20,
        'North Beach': 3,
        'Fisherman's Wharf': 8,
        'Haight-Ashbury': 19,
        'Nob Hill': 9,
        'Golden Gate Park': 23,
        'Union Square': 7,
        'Alamo Square': 17,
        'Presidio': 19,
        'Pacific Heights': 10
    },
    'Pacific Heights': {
        'Bayview': 22,
        'North Beach': 9,
        'Fisherman's Wharf': 13,
        'Haight-Ashbury': 11,
        'Nob Hill': 8,
        'Golden Gate Park': 15,
        'Union Square': 12,
        'Alamo Square': 10,
        'Presidio': 11,
        'Chinatown': 11
    }
}

people = [
    {'name': 'Brian', 'location': 'North Beach', 'start': 630, 'end': 990, 'min': 90},
    {'name': 'Richard', 'location': 'Fisherman's Wharf', 'start': 570, 'end': 690, 'min': 60},
    {'name': 'Ashley', 'location': 'Haight-Ashbury', 'start': 690, 'end': 990, 'min': 90},
    {'name': 'Elizabeth', 'location': 'Nob Hill', 'start': 330, 'end': 780, 'min': 75},
    {'name': 'Jessica', 'location': 'Golden Gate Park', 'start': 1080, 'end': 1140, 'min': 105},
    {'name': 'Deborah', 'location': 'Union Square', 'start': 330, 'end': 990, 'min': 60},
    {'name': 'Kimberly', 'location': 'Alamo Square', 'start': 330, 'end': 1140, 'min': 45},
    {'name': 'Matthew', 'location': 'Presidio', 'start': 0, 'end': 90, 'min': 15},
    {'name': 'Kenneth', 'location': 'Chinatown', 'start': 570, 'end': 990, 'min': 105},
    {'name': 'Anthony', 'location': 'Pacific Heights', 'start': 570, 'end': 780, 'min': 30}
]

people_sorted = sorted(people, key=lambda x: (x['end'] - x['min']))

current_time = 0
current_location = 'Bayview'
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