import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def calculate_schedule():
    # Travel times dictionary: {from: {to: minutes}}
    travel_times = {
        'Presidio': {
            'Haight-Ashbury': 15, 'Nob Hill': 18, 'Russian Hill': 14, 'North Beach': 18,
            'Chinatown': 21, 'Union Square': 22, 'Embarcadero': 20, 'Financial District': 23, 'Marina District': 11
        },
        'Haight-Ashbury': {
            'Presidio': 15, 'Nob Hill': 15, 'Russian Hill': 17, 'North Beach': 19,
            'Chinatown': 19, 'Union Square': 19, 'Embarcadero': 20, 'Financial District': 21, 'Marina District': 17
        },
        'Nob Hill': {
            'Presidio': 17, 'Haight-Ashbury': 13, 'Russian Hill': 5, 'North Beach': 8,
            'Chinatown': 6, 'Union Square': 7, 'Embarcadero': 9, 'Financial District': 9, 'Marina District': 11
        },
        'Russian Hill': {
            'Presidio': 14, 'Haight-Ashbury': 17, 'Nob Hill': 5, 'North Beach': 5,
            'Chinatown': 9, 'Union Square': 10, 'Embarcadero': 8, 'Financial District': 11, 'Marina District': 7
        },
        'North Beach': {
            'Presidio': 17, 'Haight-Ashbury': 18, 'Nob Hill': 7, 'Russian Hill': 4,
            'Chinatown': 6, 'Union Square': 7, 'Embarcadero': 6, 'Financial District': 8, 'Marina District': 9
        },
        'Chinatown': {
            'Presidio': 19, 'Haight-Ashbury': 19, 'Nob Hill': 9, 'Russian Hill': 7,
            'North Beach': 3, 'Union Square': 7, 'Embarcadero': 5, 'Financial District': 5, 'Marina District': 12
        },
        'Union Square': {
            'Presidio': 24, 'Haight-Ashbury': 18, 'Nob Hill': 9, 'Russian Hill': 13,
            'North Beach': 10, 'Chinatown': 7, 'Embarcadero': 11, 'Financial District': 9, 'Marina District': 18
        },
        'Embarcadero': {
            'Presidio': 20, 'Haight-Ashbury': 21, 'Nob Hill': 10, 'Russian Hill': 8,
            'North Beach': 5, 'Chinatown': 7, 'Union Square': 10, 'Financial District': 5, 'Marina District': 12
        },
        'Financial District': {
            'Presidio': 22, 'Haight-Ashbury': 19, 'Nob Hill': 8, 'Russian Hill': 11,
            'North Beach': 7, 'Chinatown': 5, 'Union Square': 9, 'Embarcadero': 4, 'Marina District': 15
        },
        'Marina District': {
            'Presidio': 10, 'Haight-Ashbury': 16, 'Nob Hill': 12, 'Russian Hill': 8,
            'North Beach': 11, 'Chinatown': 15, 'Union Square': 16, 'Embarcadero': 14, 'Financial District': 17
        }
    }

    # Friend constraints: {name: (location, available_start, available_end, min_duration)}
    friends = {
        'Karen': ('Haight-Ashbury', '21:00', '21:45', 45),
        'Jessica': ('Nob Hill', '13:45', '21:00', 90),
        'Brian': ('Russian Hill', '15:30', '21:45', 60),
        'Kenneth': ('North Beach', '9:45', '21:00', 30),
        'Jason': ('Chinatown', '8:15', '11:45', 75),
        'Stephanie': ('Union Square', '14:45', '18:45', 105),
        'Kimberly': ('Embarcadero', '9:45', '19:30', 75),
        'Steven': ('Financial District', '7:15', '21:15', 60),
        'Mark': ('Marina District', '10:15', '13:00', 75)
    }

    # Convert all times to minutes
    friends_min = {}
    for name, (loc, start, end, dur) in friends.items():
        friends_min[name] = (loc, time_to_minutes(start), time_to_minutes(end), dur)

    current_time = time_to_minutes('9:00')
    current_location = 'Presidio'
    itinerary = []
    visited = set()

    # Helper function to find next possible meeting
    def get_next_meeting(current_loc, current_time, visited):
        best_meeting = None
        best_end_time = float('inf')
        best_travel_time = 0

        for name, (loc, start, end, dur) in friends_min.items():
            if name in visited:
                continue
            travel_time = travel_times[current_loc][loc]
            arrival_time = current_time + travel_time
            meeting_start = max(arrival_time, start)
            meeting_end = meeting_start + dur
            if meeting_end <= end and meeting_end < best_end_time:
                best_meeting = name
                best_end_time = meeting_end
                best_travel_time = travel_time
                best_loc = loc
                best_dur = dur
                best_start_time = meeting_start

        if best_meeting:
            return {
                'name': best_meeting,
                'loc': best_loc,
                'start': best_start_time,
                'end': best_end_time,
                'travel_time': best_travel_time
            }
        return None

    # Try to meet as many friends as possible
    while True:
        meeting = get_next_meeting(current_location, current_time, visited)
        if not meeting:
            break

        visited.add(meeting['name'])
        itinerary.append({
            'action': 'meet',
            'location': meeting['loc'],
            'person': meeting['name'],
            'start_time': minutes_to_time(meeting['start']),
            'end_time': minutes_to_time(meeting['end'])
        })
        current_location = meeting['loc']
        current_time = meeting['end']

    # Special case for Karen (late night)
    if 'Karen' not in visited:
        travel_time = travel_times[current_location]['Haight-Ashbury']
        arrival_time = current_time + travel_time
        karen_start = max(arrival_time, time_to_minutes('21:00'))
        karen_end = karen_start + 45
        if karen_end <= time_to_minutes('21:45'):
            itinerary.append({
                'action': 'meet',
                'location': 'Haight-Ashbury',
                'person': 'Karen',
                'start_time': minutes_to_time(karen_start),
                'end_time': minutes_to_time(karen_end)
            })

    return {'itinerary': itinerary}

result = calculate_schedule()
print(json.dumps(result, indent=2))