def convert_minutes(minutes):
    hours = minutes // 60
    mins = minutes % 60
    if hours == 0:
        return '9:00'
    else:
        return f"{hours}:{mins:02d}"

locations = {
    'Richmond District': {
        'Chinatown': 20,
        'Sunset District': 11,
        'Alamo Square': 13,
        'Financial District': 22,
        'North Beach': 17,
        'Embarcadero': 19,
        'Presidio': 7,
        'Golden Gate Park': 9,
        'Bayview': 27
    },
    'Chinatown': {
        'Richmond District': 20,
        'Sunset District': 29,
        'Alamo Square': 17,
        'Financial District': 5,
        'North Beach': 3,
        'Embarcadero': 5,
        'Presidio': 19,
        'Golden Gate Park': 23,
        'Bayview': 20
    },
    'Sunset District': {
        'Richmond District': 12,
        'Chinatown': 30,
        'Alamo Square': 17,
        'Financial District': 30,
        'North Beach': 28,
        'Embarcadero': 30,
        'Presidio': 16,
        'Golden Gate Park': 11,
        'Bayview': 22
    },
    'Alamo Square': {
        'Richmond District': 11,
        'Chinatown': 15,
        'Sunset District': 16,
        'Financial District': 17,
        'North Beach': 15,
        'Embarcadero': 16,
        'Presidio': 17,
        'Golden Gate Park': 9,
        'Bayview': 16
    },
    'Financial District': {
        'Richmond District': 21,
        'Chinatown': 5,
        'Sunset District': 30,
        'Alamo Square': 17,
        'North Beach': 7,
        'Embarcadero': 4,
        'Presidio': 22,
        'Golden Gate Park': 23,
        'Bayview': 19
    },
    'North Beach': {
        'Richmond District': 18,
        'Chinatown': 6,
        'Sunset District': 27,
        'Alamo Square': 16,
        'Financial District': 8,
        'Embarcadero': 6,
        'Presidio': 17,
        'Golden Gate Park': 22,
        'Bayview': 25
    },
    'Embarcadero': {
        'Richmond District': 21,
        'Chinatown': 7,
        'Sunset District': 30,
        'Alamo Square': 19,
        'Financial District': 5,
        'North Beach': 5,
        'Presidio': 20,
        'Golden Gate Park': 25,
        'Bayview': 21
    },
    'Presidio': {
        'Richmond District': 7,
        'Chinatown': 21,
        'Sunset District': 15,
        'Alamo Square': 19,
        'Financial District': 23,
        'North Beach': 18,
        'Embarcadero': 20,
        'Golden Gate Park': 12,
        'Bayview': 31
    },
    'Golden Gate Park': {
        'Richmond District': 7,
        'Chinatown': 23,
        'Sunset District': 10,
        'Alamo Square': 9,
        'Financial District': 26,
        'North Beach': 23,
        'Embarcadero': 25,
        'Presidio': 11,
        'Bayview': 23
    },
    'Bayview': {
        'Richmond District': 25,
        'Chinatown': 19,
        'Sunset District': 23,
        'Alamo Square': 16,
        'Financial District': 19,
        'North Beach': 22,
        'Embarcadero': 19,
        'Presidio': 32,
        'Golden Gate Park': 22
    }
}

people = [
    {'name': 'Robert', 'location': 'Chinatown', 'start': 630, 'end': 990, 'min': 120},
    {'name': 'David', 'location': 'Sunset District', 'start': 570, 'end': 990, 'min': 45},
    {'name': 'Matthew', 'location': 'Alamo Square', 'start': 90, 'end': 390, 'min': 90},
    {'name': 'Jessica', 'location': 'Financial District', 'start': 90, 'end': 990, 'min': 45},
    {'name': 'Melissa', 'location': 'North Beach', 'start': 90, 'end': 720, 'min': 45},
    {'name': 'Mark', 'location': 'Embarcadero', 'start': 630, 'end': 780, 'min': 45},
    {'name': 'Deborah', 'location': 'Presidio', 'start': 990, 'end': 1080, 'min': 45},
    {'name': 'Karen', 'location': 'Golden Gate Park', 'start': 990, 'end': 1260, 'min': 120},
    {'name': 'Laura', 'location': 'Bayview', 'start': 1080, 'end': 1140, 'min': 15}
]

people_sorted = sorted(people, key=lambda x: (x['end'] - x['min']))

current_time = 0
current_location = 'Richmond District'
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