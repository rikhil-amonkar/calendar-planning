import itertools
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Sunset District'): 25,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Sunset District'): 15,
}

friends = [
    {
        'name': 'Ronald',
        'location': 'Nob Hill',
        'start_time': 600,
        'end_time': 1020,
        'duration': 105
    },
    {
        'name': 'Sarah',
        'location': 'Russian Hill',
        'start_time': 435,
        'end_time': 570,
        'duration': 45
    },
    {
        'name': 'Helen',
        'location': 'The Castro',
        'start_time': 810,
        'end_time': 1020,
        'duration': 120
    },
    {
        'name': 'Joshua',
        'location': 'Sunset District',
        'start_time': 855,
        'end_time': 1170,
        'duration': 90
    },
    {
        'name': 'Margaret',
        'location': 'Haight-Ashbury',
        'start_time': 615,
        'end_time': 1320,
        'duration': 60
    }
]

best_itinerary = []
max_met = 0

for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM in minutes
    current_location = 'Pacific Heights'
    itinerary = []
    for friend in perm:
        travel_time = travel_times.get((current_location, friend['location']))
        arrival_time = current_time + travel_time
        friend_start = friend['start_time']
        friend_end = friend['end_time']
        required_duration = friend['duration']
        earliest_start = max(arrival_time, friend_start)
        meeting_end = earliest_start + required_duration
        if meeting_end > friend_end:
            continue
        else:
            itinerary.append((friend, earliest_start, meeting_end))
            current_time = meeting_end
            current_location = friend['location']
    if len(itinerary) > max_met:
        max_met = len(itinerary)
        best_itinerary = itinerary

json_itinerary = []
for entry in best_itinerary:
    friend = entry[0]
    start = minutes_to_time_str(entry[1])
    end = minutes_to_time_str(entry[2])
    json_itinerary.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": start,
        "end_time": end
    })

result = {"itinerary": json_itinerary}

print(json.dumps(result, indent=2))