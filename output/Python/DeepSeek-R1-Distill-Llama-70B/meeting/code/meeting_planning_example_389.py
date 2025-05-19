import itertools
import json

travel_times = {
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Bayview'): 26,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Bayview'): 15,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Mission District'): 13,
}

friends = [
    {
        'name': 'Sarah',
        'location': 'Fisherman\'s Wharf',
        'start_time': 14 * 60 + 45,  # 2:45 PM
        'end_time': 17 * 60 + 30,    # 5:30 PM
        'duration': 105
    },
    {
        'name': 'Mary',
        'location': 'Richmond District',
        'start_time': 13 * 60 + 0,   # 1:00 PM
        'end_time': 19 * 60 + 15,    # 7:15 PM
        'duration': 75
    },
    {
        'name': 'Helen',
        'location': 'Mission District',
        'start_time': 21 * 60 + 45,  # 9:45 PM
        'end_time': 22 * 60 + 30,    # 10:30 PM
        'duration': 30
    },
    {
        'name': 'Thomas',
        'location': 'Bayview',
        'start_time': 15 * 60 + 15,  # 3:15 PM
        'end_time': 18 * 60 + 45,    # 6:45 PM
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
    current_location = 'Haight-Ashbury'
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