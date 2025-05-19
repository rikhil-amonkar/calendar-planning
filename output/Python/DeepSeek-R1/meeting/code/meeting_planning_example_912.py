import json

def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

travel_times = {
    'Union Square': {'Presidio': 24, 'Alamo Square': 15, 'Marina District': 18, 'Financial District': 9, 'Nob Hill': 9, 'Sunset District': 27, 'Chinatown': 7, 'Russian Hill': 13, 'North Beach': 10, 'Haight-Ashbury': 18},
    'Presidio': {'Union Square': 22, 'Alamo Square': 19, 'Marina District': 11, 'Financial District': 23, 'Nob Hill': 18, 'Sunset District': 15, 'Chinatown': 21, 'Russian Hill': 14, 'North Beach': 18, 'Haight-Ashbury': 15},
    'Alamo Square': {'Union Square': 14, 'Presidio': 17, 'Marina District': 15, 'Financial District': 17, 'Nob Hill': 11, 'Sunset District': 16, 'Chinatown': 15, 'Russian Hill': 13, 'North Beach': 15, 'Haight-Ashbury': 5},
    'Marina District': {'Union Square': 16, 'Presidio': 10, 'Alamo Square': 15, 'Financial District': 17, 'Nob Hill': 12, 'Sunset District': 19, 'Chinatown': 15, 'Russian Hill': 8, 'North Beach': 11, 'Haight-Ashbury': 16},
    'Financial District': {'Union Square': 9, 'Presidio': 22, 'Alamo Square': 17, 'Marina District': 15, 'Nob Hill': 8, 'Sunset District': 30, 'Chinatown': 5, 'Russian Hill': 11, 'North Beach': 7, 'Haight-Ashbury': 19},
    'Nob Hill': {'Union Square': 7, 'Presidio': 17, 'Alamo Square': 11, 'Marina District': 11, 'Financial District': 9, 'Sunset District': 24, 'Chinatown': 6, 'Russian Hill': 5, 'North Beach': 8, 'Haight-Ashbury': 13},
    'Sunset District': {'Union Square': 30, 'Presidio': 16, 'Alamo Square': 17, 'Marina District': 21, 'Financial District': 30, 'Nob Hill': 27, 'Chinatown': 30, 'Russian Hill': 24, 'North Beach': 28, 'Haight-Ashbury': 15},
    'Chinatown': {'Union Square': 7, 'Presidio': 19, 'Alamo Square': 17, 'Marina District': 12, 'Financial District': 5, 'Nob Hill': 9, 'Sunset District': 29, 'Russian Hill': 7, 'North Beach': 3, 'Haight-Ashbury': 19},
    'Russian Hill': {'Union Square': 10, 'Presidio': 14, 'Alamo Square': 15, 'Marina District': 7, 'Financial District': 11, 'Nob Hill': 5, 'Sunset District': 23, 'Chinatown': 9, 'North Beach': 5, 'Haight-Ashbury': 17},
    'North Beach': {'Union Square': 7, 'Presidio': 17, 'Alamo Square': 16, 'Marina District': 9, 'Financial District': 8, 'Nob Hill': 7, 'Sunset District': 27, 'Chinatown': 6, 'Russian Hill': 4, 'Haight-Ashbury': 18},
    'Haight-Ashbury': {'Union Square': 19, 'Presidio': 15, 'Alamo Square': 5, 'Marina District': 17, 'Financial District': 21, 'Nob Hill': 15, 'Sunset District': 15, 'Chinatown': 19, 'Russian Hill': 17, 'North Beach': 19}
}

friends = [
    {'name': 'Kimberly', 'location': 'Presidio', 'start': '15:30', 'end': '16:00', 'duration': 15},
    {'name': 'Elizabeth', 'location': 'Alamo Square', 'start': '19:15', 'end': '20:15', 'duration': 15},
    {'name': 'Joshua', 'location': 'Marina District', 'start': '10:30', 'end': '14:15', 'duration': 45},
    {'name': 'Sandra', 'location': 'Financial District', 'start': '19:30', 'end': '20:15', 'duration': 45},
    {'name': 'Kenneth', 'location': 'Nob Hill', 'start': '12:45', 'end': '21:45', 'duration': 30},
    {'name': 'Betty', 'location': 'Sunset District', 'start': '14:00', 'end': '19:00', 'duration': 60},
    {'name': 'Deborah', 'location': 'Chinatown', 'start': '17:15', 'end': '20:30', 'duration': 15},
    {'name': 'Barbara', 'location': 'Russian Hill', 'start': '17:30', 'end': '21:15', 'duration': 120},
    {'name': 'Steven', 'location': 'North Beach', 'start': '17:45', 'end': '20:45', 'duration': 90},
    {'name': 'Daniel', 'location': 'Haight-Ashbury', 'start': '18:30', 'end': '18:45', 'duration': 15}
]

for f in friends:
    f['start_min'] = time_to_minutes(f['start'])
    f['end_min'] = time_to_minutes(f['end'])

friends.sort(key=lambda x: x['end_min'])

current_time = time_to_minutes('9:00')
current_location = 'Union Square'
itinerary = []

for friend in friends:
    loc = friend['location']
    if current_location not in travel_times or loc not in travel_times[current_location]:
        continue
    travel_time = travel_times[current_location][loc]
    earliest_arrival = current_time + travel_time
    latest_start = friend['end_min'] - friend['duration']
    if earliest_arrival > latest_start:
        continue
    actual_start = max(earliest_arrival, friend['start_min'])
    actual_end = actual_start + friend['duration']
    if actual_end > friend['end_min']:
        continue
    itinerary.append({
        'action': 'meet',
        'location': loc,
        'person': friend['name'],
        'start_time': minutes_to_time(actual_start),
        'end_time': minutes_to_time(actual_end)
    })
    current_time = actual_end
    current_location = loc

print(json.dumps({'itinerary': itinerary}, indent=2))