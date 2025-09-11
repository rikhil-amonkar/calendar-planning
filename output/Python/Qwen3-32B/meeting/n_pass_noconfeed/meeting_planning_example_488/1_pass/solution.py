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
        'earliest_start': 10 * 60,  # 10:00 AM
        'latest_end': 17 * 60,  # 5:00 PM
        'required': 105
    },
    {
        'name': 'Margaret',
        'location': 'Haight-Ashbury',
        'earliest_start': 10 * 60 + 15,  # 10:15 AM
        'latest_end': 22 * 60,  # 10:00 PM
        'required': 60
    },
    {
        'name': 'Helen',
        'location': 'The Castro',
        'earliest_start': 13 * 60 + 30,  # 1:30 PM
        'latest_end': 17 * 60,  # 5:00 PM
        'required': 120
    },
    {
        'name': 'Joshua',
        'location': 'Sunset District',
        'earliest_start': 14 * 60 + 15,  # 2:15 PM
        'latest_end': 19 * 60 + 30,  # 7:30 PM
        'required': 90
    }
]

start_location = 'Pacific Heights'
start_time_minutes = 9 * 60  # 9:00 AM

best_itinerary = None

for r in range(len(friends), 0, -1):
    for perm in itertools.permutations(friends, r):
        current_time = start_time_minutes
        current_location = start_location
        valid = True
        itinerary = []
        for friend in perm:
            from_loc = current_location
            to_loc = friend['location']
            travel_time = travel_times.get((from_loc, to_loc), None)
            if travel_time is None:
                valid = False
                break
            arrival_time = current_time + travel_time
            earliest_start = max(arrival_time, friend['earliest_start'])
            meeting_end = earliest_start + friend['required']
            if meeting_end > friend['latest_end']:
                valid = False
                break
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time_str(earliest_start),
                'end_time': minutes_to_time_str(meeting_end)
            })
            current_time = meeting_end
            current_location = friend['location']
        if valid:
            best_itinerary = itinerary
            break
    if best_itinerary:
        break

result = {
    "itinerary": best_itinerary
}
print(json.dumps(result, indent=2))