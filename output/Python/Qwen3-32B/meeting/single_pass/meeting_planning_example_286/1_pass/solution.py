import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_time = {
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Sunset District'): 26,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Sunset District'): 24,
    ('Bayview', 'Union Square'): 17,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Sunset District'): 23,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Bayview'): 22,
}

friends = [
    {
        'name': 'Carol',
        'location': 'Sunset District',
        'start': 615,  # 10:15 AM
        'end': 645,    # 11:45 AM
        'duration': 30
    },
    {
        'name': 'Karen',
        'location': 'Bayview',
        'start': 765,  # 12:45 PM
        'end': 900,    # 3:00 PM
        'duration': 120
    },
    {
        'name': 'Rebecca',
        'location': 'Mission District',
        'start': 690,  # 11:30 AM
        'end': 1215,   # 8:15 PM
        'duration': 120
    }
]

best_itinerary = []
best_len = 0

for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM
    current_location = 'Union Square'
    meetings = []
    valid = True

    for friend in perm:
        from_loc = current_location
        to_loc = friend['location']
        if (from_loc, to_loc) in travel_time:
            travel_duration = travel_time[(from_loc, to_loc)]
        else:
            valid = False
            break
        arrival_time = current_time + travel_duration
        meeting_start = max(arrival_time, friend['start'])
        if meeting_start + friend['duration'] > friend['end']:
            valid = False
            break
        # record the meeting
        meetings.append({
            'action': 'meet',
            'location': to_loc,
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_start + friend['duration'])
        })
        current_time = meeting_start + friend['duration']
        current_location = to_loc

    if valid and len(meetings) > best_len:
        best_itinerary = meetings
        best_len = len(meetings)

result = {
    "itinerary": best_itinerary
}

print(json.dumps(result, indent=2))