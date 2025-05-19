import itertools
import json

travel_times = {
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Financial District'): 19,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Financial District'): 13,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Financial District'): 17,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Mission District'): 17,
    ('Financial District', 'Haight-Ashbury'): 19,
}

friends = [
    {
        'name': 'Mary',
        'location': 'Pacific Heights',
        'start_time': 10 * 60 + 0,   # 10:00 AM
        'end_time': 19 * 60 + 0,     # 7:00 PM
        'duration': 45
    },
    {
        'name': 'Lisa',
        'location': 'Mission District',
        'start_time': 20 * 60 + 30,  # 8:30 PM
        'end_time': 22 * 60 + 0,     # 10:00 PM
        'duration': 75
    },
    {
        'name': 'Betty',
        'location': 'Haight-Ashbury',
        'start_time': 7 * 60 + 15,   # 7:15 AM
        'end_time': 17 * 60 + 15,    # 5:15 PM
        'duration': 90
    },
    {
        'name': 'Charles',
        'location': 'Financial District',
        'start_time': 11 * 60 + 15,  # 11:15 AM
        'end_time': 15 * 60 + 0,     # 3:00 PM
        'duration': 120
    },
]

def convert_minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

best_itinerary = []
max_met = 0

for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM
    current_location = 'Bayview'
    itinerary = []
    for friend in perm:
        travel_time = travel_times.get((current_location, friend['location']), None)
        if travel_time is None:
            break
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, friend['start_time'])
        meeting_end = meeting_start + friend['duration']
        if meeting_end > friend['end_time']:
            break
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': convert_minutes_to_time(meeting_start),
            'end_time': convert_minutes_to_time(meeting_end)
        })
        current_time = meeting_end
        current_location = friend['location']
    if len(itinerary) > max_met:
        max_met = len(itinerary)
        best_itinerary = itinerary

output = {
    "itinerary": best_itinerary
}

print(json.dumps(output, indent=2))