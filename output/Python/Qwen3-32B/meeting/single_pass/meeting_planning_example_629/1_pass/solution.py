import itertools
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define friends with their constraints
friends = [
    {
        'name': 'Matthew',
        'location': 'Presidio',
        'available_start': 660,  # 11:00 AM
        'available_end': 1260,   # 9:00 PM
        'duration': 90
    },
    {
        'name': 'Margaret',
        'location': 'Chinatown',
        'available_start': 555,  # 9:15 AM
        'available_end': 1125,   # 6:45 PM
        'duration': 90
    },
    {
        'name': 'Nancy',
        'location': 'Pacific Heights',
        'available_start': 855,  # 2:15 PM
        'available_end': 1020,   # 5:00 PM
        'duration': 15
    },
    {
        'name': 'Helen',
        'location': 'Richmond District',
        'available_start': 1185,  # 7:45 PM
        'available_end': 1320,    # 10:00 PM
        'duration': 60
    },
    {
        'name': 'Rebecca',
        'location': "Fisherman's Wharf",
        'available_start': 1275,  # 9:15 PM
        'available_end': 1335,    # 10:15 PM
        'duration': 60
    },
    {
        'name': 'Kimberly',
        'location': 'Golden Gate Park',
        'available_start': 780,   # 1:00 PM
        'available_end': 990,     # 4:30 PM
        'duration': 120
    },
    {
        'name': 'Kenneth',
        'location': 'Bayview',
        'available_start': 870,   # 2:30 PM
        'available_end': 1080,    # 6:00 PM
        'duration': 60
    }
]

# Define travel times between locations
travel_times = {
    'Russian Hill': {
        'Presidio': 14,
        'Chinatown': 9,
        'Pacific Heights': 7,
        'Richmond District': 14,
        "Fisherman's Wharf": 7,
        'Golden Gate Park': 21,
        'Bayview': 23
    },
    'Presidio': {
        'Russian Hill': 14,
        'Chinatown': 21,
        'Pacific Heights': 11,
        'Richmond District': 7,
        "Fisherman's Wharf": 19,
        'Golden Gate Park': 12,
        'Bayview': 31
    },
    'Chinatown': {
        'Russian Hill': 7,
        'Presidio': 19,
        'Pacific Heights': 10,
        'Richmond District': 20,
        "Fisherman's Wharf": 8,
        'Golden Gate Park': 23,
        'Bayview': 22
    },
    'Pacific Heights': {
        'Russian Hill': 7,
        'Presidio': 11,
        'Chinatown': 11,
        'Richmond District': 12,
        "Fisherman's Wharf": 13,
        'Golden Gate Park': 15,
        'Bayview': 22
    },
    'Richmond District': {
        'Russian Hill': 13,
        'Presidio': 7,
        'Chinatown': 20,
        'Pacific Heights': 10,
        "Fisherman's Wharf": 18,
        'Golden Gate Park': 9,
        'Bayview': 26
    },
    "Fisherman's Wharf": {
        'Russian Hill': 7,
        'Presidio': 17,
        'Chinatown': 12,
        'Pacific Heights': 12,
        'Richmond District': 18,
        'Golden Gate Park': 25,
        'Bayview': 26
    },
    'Golden Gate Park': {
        'Russian Hill': 19,
        'Presidio': 11,
        'Chinatown': 23,
        'Pacific Heights': 16,
        'Richmond District': 7,
        "Fisherman's Wharf": 24,
        'Bayview': 23
    },
    'Bayview': {
        'Russian Hill': 23,
        'Presidio': 31,
        'Chinatown': 18,
        'Pacific Heights': 23,
        'Richmond District': 25,
        "Fisherman's Wharf": 25,
        'Golden Gate Park': 22
    }
}

def is_valid_sequence(perm):
    current_time = 540  # 9:00 AM
    current_location = 'Russian Hill'
    meetings = []
    for friend in perm:
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        available_start = friend['available_start']
        available_end = friend['available_end']
        duration = friend['duration']
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + duration
        if meeting_end > available_end:
            return False, None
        meetings.append({
            'person': friend['name'],
            'location': friend['location'],
            'start_time': meeting_start,
            'end_time': meeting_end
        })
        current_time = meeting_end
        current_location = friend['location']
    return True, meetings

best_sequence = None
max_meetings = 0
earliest_end = float('inf')

for k in range(1, len(friends) + 1):
    for perm in itertools.permutations(friends, k):
        is_valid, meetings = is_valid_sequence(perm)
        if is_valid:
            num_meetings = len(meetings)
            if num_meetings > max_meetings:
                max_meetings = num_meetings
                best_sequence = meetings
                earliest_end = meetings[-1]['end_time'] if meetings else 0
            elif num_meetings == max_meetings:
                current_end = meetings[-1]['end_time'] if meetings else 0
                if current_end < earliest_end:
                    best_sequence = meetings
                    earliest_end = current_end

# Convert best_sequence to the required JSON format
itinerary = []
for meeting in best_sequence:
    itinerary.append({
        "action": "meet",
        "location": meeting['location'],
        "person": meeting['person'],
        "start_time": minutes_to_time_str(meeting['start_time']),
        "end_time": minutes_to_time_str(meeting['end_time'])
    })

result = {
    "itinerary": itinerary
}

print(json.dumps(result, indent=2))