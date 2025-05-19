def convert_minutes(minutes):
    hours = minutes // 60
    mins = minutes % 60
    if hours == 0:
        return '9:00'
    else:
        return f"{hours}:{mins:02d}"

locations = {
    'Union Square': {
        'The Castro': 17,
        'North Beach': 10,
        'Embarcadero': 11,
        'Alamo Square': 15,
        'Nob Hill': 9,
        'Presidio': 24,
        'Fisherman's Wharf': 15,
        'Mission District': 14,
        'Haight-Ashbury': 18
    },
    'The Castro': {
        'Union Square': 19,
        'North Beach': 20,
        'Embarcadero': 22,
        'Alamo Square': 8,
        'Nob Hill': 16,
        'Presidio': 20,
        'Fisherman's Wharf': 24,
        'Mission District': 7,
        'Haight-Ashbury': 6
    },
    'North Beach': {
        'Union Square': 7,
        'The Castro': 23,
        'Embarcadero': 6,
        'Alamo Square': 16,
        'Nob Hill': 7,
        'Presidio': 17,
        'Fisherman's Wharf': 5,
        'Mission District': 18,
        'Haight-Ashbury': 18
    },
    'Embarcadero': {
        'Union Square': 10,
        'The Castro': 25,
        'North Beach': 5,
        'Alamo Square': 19,
        'Nob Hill': 10,
        'Presidio': 20,
        'Fisherman's Wharf': 6,
        'Mission District': 20,
        'Haight-Ashbury': 21
    },
    'Alamo Square': {
        'Union Square': 14,
        'The Castro': 8,
        'North Beach': 15,
        'Embarcadero': 16,
        'Nob Hill': 11,
        'Presidio': 17,
        'Fisherman's Wharf': 19,
        'Mission District': 10,
        'Haight-Ashbury': 5
    },
    'Nob Hill': {
        'Union Square': 7,
        'The Castro': 17,
        'North Beach': 8,
        'Embarcadero': 9,
        'Alamo Square': 11,
        'Presidio': 17,
        'Fisherman's Wharf': 10,
        'Mission District': 13,
        'Haight-Ashbury': 13
    },
    'Presidio': {
        'Union Square': 22,
        'The Castro': 21,
        'North Beach': 18,
        'Embarcadero': 20,
        'Alamo Square': 19,
        'Nob Hill': 18,
        'Fisherman's Wharf': 19,
        'Mission District': 26,
        'Haight-Ashbury': 15
    },
    'Fisherman's Wharf': {
        'Union Square': 13,
        'The Castro': 27,
        'North Beach': 6,
        'Embarcadero': 8,
        'Alamo Square': 21,
        'Nob Hill': 11,
        'Presidio': 17,
        'Mission District': 22,
        'Haight-Ashbury': 22
    },
    'Mission District': {
        'Union Square': 15,
        'The Castro': 7,
        'North Beach': 17,
        'Embarcadero': 19,
        'Alamo Square': 11,
        'Nob Hill': 12,
        'Presidio': 25,
        'Fisherman's Wharf': 22,
        'Haight-Ashbury': 12
    },
    'Haight-Ashbury': {
        'Union Square': 19,
        'The Castro': 6,
        'North Beach': 19,
        'Embarcadero': 20,
        'Alamo Square': 5,
        'Nob Hill': 15,
        'Presidio': 15,
        'Fisherman's Wharf': 23,
        'Mission District': 11
    }
}

people = [
    {'name': 'Melissa', 'location': 'The Castro', 'start': 630, 'end': 720, 'min': 30},
    {'name': 'Kimberly', 'location': 'North Beach', 'start': 450, 'end': 690, 'min': 15},
    {'name': 'Joseph', 'location': 'Embarcadero', 'start': 390, 'end': 630, 'min': 75},
    {'name': 'Barbara', 'location': 'Alamo Square', 'start': 735, 'end': 810, 'min': 15},
    {'name': 'Kenneth', 'location': 'Nob Hill', 'start': 615, 'end': 1050, 'min': 105},
    {'name': 'Joshua', 'location': 'Presidio', 'start': 690, 'end': 1050, 'min': 105},
    {'name': 'Brian', 'location': 'Fisherman's Wharf', 'start': 570, 'end': 990, 'min': 45},
    {'name': 'Steven', 'location': 'Mission District', 'start': 990, 'end': 1050, 'min': 90},
    {'name': 'Betty', 'location': 'Haight-Ashbury', 'start': 990, 'end': 1050, 'min': 90},
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