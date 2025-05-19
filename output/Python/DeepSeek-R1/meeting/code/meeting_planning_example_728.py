import json
import itertools

def time_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    ('Marina District', 'Mission District'): 20,
    ('Marina District', 'Fisherman\'s Wharf'): 10,
    ('Marina District', 'Presidio'): 10,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Russian Hill'): 8,
    ('Mission District', 'Marina District'): 19,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Financial District'): 15,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Russian Hill'): 15,
    ('Fisherman\'s Wharf', 'Marina District'): 9,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Russian Hill'): 14,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Presidio'): 24,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Russian Hill'): 13,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Mission District'): 25,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Russian Hill'): 24,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Mission District'): 17,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Russian Hill'): 11,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Union Square'): 19,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Haight-Ashbury'): 17,
}

friends = [
    {'name': 'Karen', 'location': 'Mission District', 'start': 855, 'end': 1320, 'duration': 30},
    {'name': 'Richard', 'location': 'Fisherman\'s Wharf', 'start': 870, 'end': 1050, 'duration': 30},
    {'name': 'Robert', 'location': 'Presidio', 'start': 1305, 'end': 1365, 'duration': 60},
    {'name': 'Joseph', 'location': 'Union Square', 'start': 705, 'end': 885, 'duration': 120},
    {'name': 'Helen', 'location': 'Sunset District', 'start': 885, 'end': 1245, 'duration': 105},
    {'name': 'Elizabeth', 'location': 'Financial District', 'start': 600, 'end': 765, 'duration': 75},
    {'name': 'Kimberly', 'location': 'Haight-Ashbury', 'start': 855, 'end': 1050, 'duration': 105},
    {'name': 'Ashley', 'location': 'Russian Hill', 'start': 690, 'end': 1290, 'duration': 45},
]

best_schedule = []
max_friends = 0
best_end_time = float('inf')

for perm in itertools.permutations(friends):
    current_time = 540
    current_location = 'Marina District'
    scheduled = []
    for friend in perm:
        from_loc = current_location
        to_loc = friend['location']
        travel_time = travel_times.get((from_loc, to_loc), 0)
        arrival_time = current_time + travel_time
        available_start = friend['start']
        available_end = friend['end']
        duration = friend['duration']
        earliest_start = max(arrival_time, available_start)
        latest_start = available_end - duration
        if earliest_start > latest_start:
            continue
        meeting_start = earliest_start
        meeting_end = meeting_start + duration
        scheduled.append({
            'friend': friend,
            'start': meeting_start,
            'end': meeting_end,
        })
        current_time = meeting_end
        current_location = to_loc
    if len(scheduled) > max_friends or (len(scheduled) == max_friends and current_time < best_end_time):
        max_friends = len(scheduled)
        best_schedule = scheduled.copy()
        best_end_time = current_time

itinerary = []
for entry in best_schedule:
    friend = entry['friend']
    itinerary.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": time_to_str(entry['start']),
        "end_time": time_to_str(entry['end'])
    })

print(json.dumps({"itinerary": itinerary}, indent=2))