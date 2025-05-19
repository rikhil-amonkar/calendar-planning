import itertools
import json

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02}"

travel_times = {
    'Haight-Ashbury': {'Russian Hill': 17, 'Fisherman\'s Wharf': 23, 'Nob Hill': 15, 'Golden Gate Park': 7, 'Alamo Square': 5, 'Pacific Heights': 12},
    'Russian Hill': {'Haight-Ashbury': 17, 'Fisherman\'s Wharf': 7, 'Nob Hill': 5, 'Golden Gate Park': 21, 'Alamo Square': 15, 'Pacific Heights': 7},
    'Fisherman\'s Wharf': {'Haight-Ashbury': 22, 'Russian Hill': 7, 'Nob Hill': 11, 'Golden Gate Park': 25, 'Alamo Square': 20, 'Pacific Heights': 12},
    'Nob Hill': {'Haight-Ashbury': 13, 'Russian Hill': 5, 'Fisherman\'s Wharf': 11, 'Golden Gate Park': 17, 'Alamo Square': 11, 'Pacific Heights': 8},
    'Golden Gate Park': {'Haight-Ashbury': 7, 'Russian Hill': 19, 'Fisherman\'s Wharf': 24, 'Nob Hill': 20, 'Alamo Square': 10, 'Pacific Heights': 16},
    'Alamo Square': {'Haight-Ashbury': 5, 'Russian Hill': 13, 'Fisherman\'s Wharf': 19, 'Nob Hill': 11, 'Golden Gate Park': 9, 'Pacific Heights': 10},
    'Pacific Heights': {'Haight-Ashbury': 11, 'Russian Hill': 7, 'Fisherman\'s Wharf': 13, 'Nob Hill': 8, 'Golden Gate Park': 15, 'Alamo Square': 10}
}

friends = [
    {'name': 'Stephanie', 'location': 'Russian Hill', 'start': 20*60, 'end': 20*60+45, 'duration': 15},
    {'name': 'Kevin', 'location': 'Fisherman\'s Wharf', 'start': 19*60+15, 'end': 21*60+45, 'duration': 75},
    {'name': 'Steven', 'location': 'Golden Gate Park', 'start': 8*60+30, 'end': 17*60, 'duration': 75},
    {'name': 'Anthony', 'location': 'Alamo Square', 'start': 7*60+45, 'end': 19*60+45, 'duration': 15},
    {'name': 'Sandra', 'location': 'Pacific Heights', 'start': 14*60+45, 'end': 21*60+45, 'duration': 45}
]

best_schedule = []
max_meetings = 0
max_duration = 0

for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM
    current_loc = 'Haight-Ashbury'
    meetings = []
    for friend in perm:
        travel = travel_times[current_loc].get(friend['location'], float('inf'))
        arrival = current_time + travel
        if arrival > friend['end']:
            continue
        earliest_start = max(arrival, friend['start'])
        latest_start = friend['end'] - friend['duration']
        if earliest_start > latest_start:
            continue
        start = earliest_start
        end = start + friend['duration']
        meetings.append({
            'person': friend['name'],
            'location': friend['location'],
            'start': start,
            'end': end
        })
        current_time = end
        current_loc = friend['location']
    num_meetings = len(meetings)
    total_duration = sum(m['end'] - m['start'] for m in meetings)
    if num_meetings > max_meetings or (num_meetings == max_meetings and total_duration > max_duration):
        max_meetings = num_meetings
        max_duration = total_duration
        best_schedule = meetings.copy()

itinerary = []
for meet in best_schedule:
    itinerary.append({
        "action": "meet",
        "location": meet['location'],
        "person": meet['person'],
        "start_time": format_time(meet['start']),
        "end_time": format_time(meet['end'])
    })

print(json.dumps({"itinerary": itinerary}, indent=2))