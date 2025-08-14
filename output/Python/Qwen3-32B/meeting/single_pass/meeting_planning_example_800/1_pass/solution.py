import itertools
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

friends = [
    {'name': 'Kimberly', 'location': 'North Beach', 'start': 420, 'end': 630, 'duration': 15},
    {'name': 'Brian', 'location': "Fisherman's Wharf", 'start': 570, 'end': 930, 'duration': 45},
    {'name': 'Kenneth', 'location': 'Nob Hill', 'start': 735, 'end': 1035, 'duration': 105},
    {'name': 'Joseph', 'location': 'Embarcadero', 'start': 930, 'end': 1170, 'duration': 75},
    {'name': 'Joshua', 'location': 'Presidio', 'start': 990, 'end': 1095, 'duration': 105},
    {'name': 'Steven', 'location': 'Mission District', 'start': 1170, 'end': 1260, 'duration': 90},
    {'name': 'Melissa', 'location': 'The Castro', 'start': 1215, 'end': 1275, 'duration': 30},
    {'name': 'Barbara', 'location': 'Alamo Square', 'start': 1245, 'end': 1305, 'duration': 15},
    {'name': 'Betty', 'location': 'Haight-Ashbury', 'start': 1140, 'end': 1230, 'duration': 90}
]

travel_times = {
    'Union Square': {
        'The Castro': 17,
        'North Beach': 10,
        'Embarcadero': 11,
        'Alamo Square': 15,
        'Nob Hill': 9,
        'Presidio': 24,
        "Fisherman's Wharf": 15,
        'Mission District': 14,
        'Haight-Ashbury': 18,
    },
    'The Castro': {
        'Union Square': 19,
        'North Beach': 20,
        'Embarcadero': 22,
        'Alamo Square': 8,
        'Nob Hill': 16,
        'Presidio': 20,
        "Fisherman's Wharf": 24,
        'Mission District': 7,
        'Haight-Ashbury': 6,
    },
    'North Beach': {
        'Union Square': 7,
        'The Castro': 23,
        'Embarcadero': 6,
        'Alamo Square': 16,
        'Nob Hill': 7,
        'Presidio': 17,
        "Fisherman's Wharf": 5,
        'Mission District': 18,
        'Haight-Ashbury': 18,
    },
    'Embarcadero': {
        'Union Square': 10,
        'The Castro': 25,
        'North Beach': 5,
        'Alamo Square': 19,
        'Nob Hill': 10,
        'Presidio': 20,
        "Fisherman's Wharf": 6,
        'Mission District': 20,
        'Haight-Ashbury': 21,
    },
    'Alamo Square': {
        'Union Square': 14,
        'The Castro': 8,
        'North Beach': 15,
        'Embarcadero': 16,
        'Nob Hill': 11,
        'Presidio': 17,
        "Fisherman's Wharf": 19,
        'Mission District': 10,
        'Haight-Ashbury': 5,
    },
    'Nob Hill': {
        'Union Square': 7,
        'The Castro': 17,
        'North Beach': 8,
        'Embarcadero': 9,
        'Alamo Square': 11,
        'Presidio': 17,
        "Fisherman's Wharf": 10,
        'Mission District': 13,
        'Haight-Ashbury': 13,
    },
    'Presidio': {
        'Union Square': 22,
        'The Castro': 21,
        'North Beach': 18,
        'Embarcadero': 20,
        'Alamo Square': 19,
        'Nob Hill': 18,
        "Fisherman's Wharf": 19,
        'Mission District': 26,
        'Haight-Ashbury': 15,
    },
    "Fisherman's Wharf": {
        'Union Square': 13,
        'The Castro': 27,
        'North Beach': 6,
        'Embarcadero': 8,
        'Alamo Square': 21,
        'Nob Hill': 11,
        'Presidio': 17,
        'Mission District': 22,
        'Haight-Ashbury': 22,
    },
    'Mission District': {
        'Union Square': 15,
        'The Castro': 7,
        'North Beach': 17,
        'Embarcadero': 19,
        'Alamo Square': 11,
        'Nob Hill': 12,
        'Presidio': 25,
        "Fisherman's Wharf": 22,
        'Haight-Ashbury': 12,
    },
    'Haight-Ashbury': {
        'Union Square': 19,
        'The Castro': 6,
        'North Beach': 19,
        'Embarcadero': 20,
        'Alamo Square': 5,
        'Nob Hill': 15,
        'Presidio': 15,
        "Fisherman's Wharf": 23,
        'Mission District': 11,
    },
}

best_meetings = []
max_meetings = 0

for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM
    current_location = 'Union Square'
    meetings = []
    valid = True
    for friend in perm:
        try:
            travel_time = travel_times[current_location][friend['location']]
        except KeyError:
            valid = False
            break
        arrival_time = current_time + travel_time
        possible_start = max(arrival_time, friend['start'])
        possible_end = possible_start + friend['duration']
        if possible_end > friend['end']:
            valid = False
            break
        meetings.append({
            'person': friend['name'],
            'location': friend['location'],
            'start_time': possible_start,
            'end_time': possible_end
        })
        current_time = possible_end
        current_location = friend['location']
    if valid:
        if len(meetings) > max_meetings:
            max_meetings = len(meetings)
            best_meetings = meetings
        elif len(meetings) == max_meetings and max_meetings > 0:
            current_total_time = meetings[-1]['end_time'] if meetings else 0
            best_total_time = best_meetings[-1]['end_time'] if best_meetings else 0
            if current_total_time < best_total_time:
                best_meetings = meetings

itinerary = []
for meeting in best_meetings:
    start_str = minutes_to_time_str(meeting['start_time'])
    end_str = minutes_to_time_str(meeting['end_time'])
    itinerary.append({
        "action": "meet",
        "location": meeting['location'],
        "person": meeting['person'],
        "start_time": start_str,
        "end_time": end_str
    })

result = {"itinerary": itinerary}

print(json.dumps(result, indent=2))