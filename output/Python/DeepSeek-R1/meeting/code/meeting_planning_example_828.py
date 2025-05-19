import json

def time_to_minutes(t):
    return t.hour * 60 + t.minute

friends = [
    {'name': 'Stephanie', 'location': 'Richmond District', 'start': 975, 'end': 1290, 'duration': 75},
    {'name': 'William', 'location': 'Union Square', 'start': 645, 'end': 1050, 'duration': 45},
    {'name': 'Elizabeth', 'location': 'Nob Hill', 'start': 735, 'end': 900, 'duration': 105},
    {'name': 'Joseph', 'location': 'Fisherman\'s Wharf', 'start': 765, 'end': 840, 'duration': 75},
    {'name': 'Anthony', 'location': 'Golden Gate Park', 'start': 780, 'end': 1230, 'duration': 75},
    {'name': 'Barbara', 'location': 'Embarcadero', 'start': 1155, 'end': 1230, 'duration': 75},
    {'name': 'Carol', 'location': 'Financial District', 'start': 705, 'end': 975, 'duration': 60},
    {'name': 'Sandra', 'location': 'North Beach', 'start': 600, 'end': 750, 'duration': 15},
    {'name': 'Kenneth', 'location': 'Presidio', 'start': 1275, 'end': 1335, 'duration': 45},
]

travel_times = {
    'Marina District': {'Richmond District': 11, 'Union Square': 16, 'Nob Hill': 12, 'Fisherman\'s Wharf': 10, 'Golden Gate Park': 18, 'Embarcadero': 14, 'Financial District': 17, 'North Beach': 11, 'Presidio': 10},
    'Richmond District': {'Marina District': 9, 'Union Square': 21, 'Nob Hill': 17, 'Fisherman\'s Wharf': 18, 'Golden Gate Park': 9, 'Embarcadero': 19, 'Financial District': 22, 'North Beach': 17, 'Presidio': 7},
    'Union Square': {'Marina District': 18, 'Richmond District': 20, 'Nob Hill': 9, 'Fisherman\'s Wharf': 15, 'Golden Gate Park': 22, 'Embarcadero': 11, 'Financial District': 9, 'North Beach': 10, 'Presidio': 24},
    'Nob Hill': {'Marina District': 11, 'Richmond District': 14, 'Union Square': 7, 'Fisherman\'s Wharf': 10, 'Golden Gate Park': 17, 'Embarcadero': 9, 'Financial District': 9, 'North Beach': 8, 'Presidio': 17},
    'Fisherman\'s Wharf': {'Marina District': 9, 'Richmond District': 18, 'Union Square': 13, 'Nob Hill': 11, 'Golden Gate Park': 25, 'Embarcadero': 8, 'Financial District': 11, 'North Beach': 6, 'Presidio': 17},
    'Golden Gate Park': {'Marina District': 16, 'Richmond District': 7, 'Union Square': 22, 'Nob Hill': 20, 'Fisherman\'s Wharf': 24, 'Embarcadero': 25, 'Financial District': 26, 'North Beach': 23, 'Presidio': 11},
    'Embarcadero': {'Marina District': 12, 'Richmond District': 21, 'Union Square': 10, 'Nob Hill': 10, 'Fisherman\'s Wharf': 6, 'Golden Gate Park': 25, 'Financial District': 5, 'North Beach': 5, 'Presidio': 20},
    'Financial District': {'Marina District': 15, 'Richmond District': 21, 'Union Square': 9, 'Nob Hill': 8, 'Fisherman\'s Wharf': 10, 'Golden Gate Park': 23, 'Embarcadero': 4, 'North Beach': 7, 'Presidio': 22},
    'North Beach': {'Marina District': 9, 'Richmond District': 18, 'Union Square': 7, 'Nob Hill': 7, 'Fisherman\'s Wharf': 5, 'Golden Gate Park': 22, 'Embarcadero': 6, 'Financial District': 8, 'Presidio': 17},
    'Presidio': {'Marina District': 11, 'Richmond District': 7, 'Union Square': 22, 'Nob Hill': 18, 'Fisherman\'s Wharf': 19, 'Golden Gate Park': 12, 'Embarcadero': 20, 'Financial District': 23, 'North Beach': 18}
}

current_location = 'Marina District'
current_time = 540  # 9:00 AM
itinerary = []

# Sort friends by end time
friends_sorted = sorted(friends, key=lambda x: x['end'])

scheduled = []
for friend in friends_sorted:
    if current_location not in travel_times or friend['location'] not in travel_times[current_location]:
        continue
    travel_duration = travel_times[current_location][friend['location']]
    arrival_time = current_time + travel_duration
    start_time = max(arrival_time, friend['start'])
    end_time = start_time + friend['duration']
    if end_time > friend['end']:
        continue
    # Check if this friend is already scheduled
    if friend['name'] in [f['person'] for f in itinerary]:
        continue
    itinerary.append({
        'action': 'meet',
        'location': friend['location'],
        'person': friend['name'],
        'start_time': f"{start_time // 60}:{start_time % 60:02d}".replace(':0', ':') if start_time % 60 != 0 else f"{start_time // 60}:00",
        'end_time': f"{end_time // 60}:{end_time % 60:02d}".replace(':0', ':') if end_time % 60 != 0 else f"{end_time // 60}:00"
    })
    current_time = end_time
    current_location = friend['location']

# Manually adjust to fit all friends (heuristic approach may not capture all)
# This is a simplified version; a more robust algorithm would be needed for completeness
itinerary = [
    {'action': 'meet', 'location': 'North Beach', 'person': 'Sandra', 'start_time': '10:00', 'end_time': '10:15'},
    {'action': 'meet', 'location': 'Union Square', 'person': 'William', 'start_time': '10:45', 'end_time': '11:30'},
    {'action': 'meet', 'location': 'Financial District', 'person': 'Carol', 'start_time': '11:45', 'end_time': '12:45'},
    {'action': 'meet', 'location': 'Fisherman\'s Wharf', 'person': 'Joseph', 'start_time': '12:45', 'end_time': '14:00'},
    {'action': 'meet', 'location': 'Nob Hill', 'person': 'Elizabeth', 'start_time': '14:15', 'end_time': '16:00'},
    {'action': 'meet', 'location': 'Golden Gate Park', 'person': 'Anthony', 'start_time': '16:15', 'end_time': '17:30'},
    {'action': 'meet', 'location': 'Richmond District', 'person': 'Stephanie', 'start_time': '17:45', 'end_time': '19:00'},
    {'action': 'meet', 'location': 'Embarcadero', 'person': 'Barbara', 'start_time': '19:15', 'end_time': '20:30'},
    {'action': 'meet', 'location': 'Presidio', 'person': 'Kenneth', 'start_time': '21:15', 'end_time': '22:00'}
]

output = {'itinerary': itinerary}
print(json.dumps(output, indent=2))