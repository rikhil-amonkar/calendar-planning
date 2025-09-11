import itertools
import json

def min_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    'Pacific Heights': {
        'Golden Gate Park': 15,
        'The Castro': 16,
        'Bayview': 22,
        'Marina District': 6,
        'Union Square': 12,
        'Sunset District': 21,
        'Alamo Square': 10,
        'Financial District': 13,
        'Mission District': 15
    },
    'Golden Gate Park': {
        'Pacific Heights': 16,
        'The Castro': 13,
        'Bayview': 23,
        'Marina District': 16,
        'Union Square': 22,
        'Sunset District': 10,
        'Alamo Square': 9,
        'Financial District': 26,
        'Mission District': 17
    },
    'The Castro': {
        'Pacific Heights': 16,
        'Golden Gate Park': 11,
        'Bayview': 19,
        'Marina District': 21,
        'Union Square': 19,
        'Sunset District': 17,
        'Alamo Square': 8,
        'Financial District': 21,
        'Mission District': 7
    },
    'Bayview': {
        'Pacific Heights': 23,
        'Golden Gate Park': 22,
        'The Castro': 19,
        'Marina District': 27,
        'Union Square': 18,
        'Sunset District': 23,
        'Alamo Square': 16,
        'Financial District': 19,
        'Mission District': 13
    },
    'Marina District': {
        'Pacific Heights': 7,
        'Golden Gate Park': 18,
        'The Castro': 22,
        'Bayview': 27,
        'Union Square': 16,
        'Sunset District': 19,
        'Alamo Square': 15,
        'Financial District': 17,
        'Mission District': 20
    },
    'Union Square': {
        'Pacific Heights': 15,
        'Golden Gate Park': 22,
        'The Castro': 17,
        'Bayview': 15,
        'Marina District': 18,
        'Sunset District': 27,
        'Alamo Square': 15,
        'Financial District': 9,
        'Mission District': 14
    },
    'Sunset District': {
        'Pacific Heights': 21,
        'Golden Gate Park': 11,
        'The Castro': 17,
        'Bayview': 22,
        'Marina District': 21,
        'Union Square': 30,
        'Alamo Square': 17,
        'Financial District': 30,
        'Mission District': 25
    },
    'Alamo Square': {
        'Pacific Heights': 10,
        'Golden Gate Park': 9,
        'The Castro': 8,
        'Bayview': 16,
        'Marina District': 15,
        'Union Square': 14,
        'Sunset District': 16,
        'Financial District': 17,
        'Mission District': 10
    },
    'Financial District': {
        'Pacific Heights': 13,
        'Golden Gate Park': 23,
        'The Castro': 20,
        'Bayview': 19,
        'Marina District': 15,
        'Union Square': 9,
        'Sunset District': 30,
        'Alamo Square': 17,
        'Mission District': 17
    },
    'Mission District': {
        'Pacific Heights': 16,
        'Golden Gate Park': 17,
        'The Castro': 7,
        'Bayview': 14,
        'Marina District': 19,
        'Union Square': 15,
        'Sunset District': 24,
        'Alamo Square': 11,
        'Financial District': 15
    }
}

friends = [
    {'name': 'Helen', 'location': 'Golden Gate Park', 'start_avail': 570, 'end_avail': 735, 'min_duration': 45},
    {'name': 'Steven', 'location': 'The Castro', 'start_avail': 1215, 'end_avail': 1320, 'min_duration': 105},
    {'name': 'Deborah', 'location': 'Bayview', 'start_avail': 510, 'end_avail': 720, 'min_duration': 30},
    {'name': 'Matthew', 'location': 'Marina District', 'start_avail': 555, 'end_avail': 855, 'min_duration': 45},
    {'name': 'Joseph', 'location': 'Union Square', 'start_avail': 855, 'end_avail': 1125, 'min_duration': 120},
    {'name': 'Ronald', 'location': 'Sunset District', 'start_avail': 960, 'end_avail': 1245, 'min_duration': 60},
    {'name': 'Robert', 'location': 'Alamo Square', 'start_avail': 1110, 'end_avail': 1275, 'min_duration': 120},
    {'name': 'Rebecca', 'location': 'Financial District', 'start_avail': 885, 'end_avail': 975, 'min_duration': 30},
    {'name': 'Elizabeth', 'location': 'Mission District', 'start_avail': 1110, 'end_avail': 1260, 'min_duration': 120}
]

best_count = 0
best_schedule = None

for perm in itertools.permutations(friends):
    current_time = 540
    current_location = 'Pacific Heights'
    schedule = []
    count = 0
    for friend in perm:
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        start_meeting = max(arrival_time, friend['start_avail'])
        end_meeting = start_meeting + friend['min_duration']
        if end_meeting <= friend['end_avail']:
            schedule.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': min_to_time(start_meeting),
                'end_time': min_to_time(end_meeting)
            })
            current_time = end_meeting
            current_location = friend['location']
            count += 1
        else:
            continue

    if count > best_count:
        best_count = count
        best_schedule = schedule

output = {"itinerary": best_schedule}
print(json.dumps(output, indent=2))