import itertools
import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours}:{minutes:02d}"

travel_times = {
    "North Beach": {
        "Pacific Heights": 8,
        "Chinatown": 6,
        "Union Square": 7,
        "Mission District": 18,
        "Golden Gate Park": 22,
        "Nob Hill": 7
    },
    "Pacific Heights": {
        "North Beach": 9,
        "Chinatown": 11,
        "Union Square": 12,
        "Mission District": 15,
        "Golden Gate Park": 15,
        "Nob Hill": 8
    },
    "Chinatown": {
        "North Beach": 3,
        "Pacific Heights": 10,
        "Union Square": 7,
        "Mission District": 18,
        "Golden Gate Park": 23,
        "Nob Hill": 8
    },
    "Union Square": {
        "North Beach": 10,
        "Pacific Heights": 15,
        "Chinatown": 7,
        "Mission District": 14,
        "Golden Gate Park": 22,
        "Nob Hill": 9
    },
    "Mission District": {
        "North Beach": 17,
        "Pacific Heights": 16,
        "Chinatown": 16,
        "Union Square": 15,
        "Golden Gate Park": 17,
        "Nob Hill": 12
    },
    "Golden Gate Park": {
        "North Beach": 24,
        "Pacific Heights": 16,
        "Chinatown": 23,
        "Union Square": 22,
        "Mission District": 17,
        "Nob Hill": 20
    },
    "Nob Hill": {
        "North Beach": 8,
        "Pacific Heights": 8,
        "Chinatown": 6,
        "Union Square": 7,
        "Mission District": 13,
        "Golden Gate Park": 17
    }
}

meetings = [
    {'person': 'James', 'location': 'Pacific Heights', 'start_str': '20:00', 'end_str': '22:00', 'min_duration': 120},
    {'person': 'Robert', 'location': 'Chinatown', 'start_str': '12:15', 'end_str': '16:45', 'min_duration': 90},
    {'person': 'Jeffrey', 'location': 'Union Square', 'start_str': '9:30', 'end_str': '15:30', 'min_duration': 120},
    {'person': 'Carol', 'location': 'Mission District', 'start_str': '18:15', 'end_str': '21:15', 'min_duration': 15},
    {'person': 'Mark', 'location': 'Golden Gate Park', 'start_str': '11:30', 'end_str': '17:45', 'min_duration': 15},
    {'person': 'Sandra', 'location': 'Nob Hill', 'start_str': '8:00', 'end_str': '15:30', 'min_duration': 15}
]

for meeting in meetings:
    meeting['available_start'] = time_to_minutes(meeting['start_str'])
    meeting['available_end'] = time_to_minutes(meeting['end_str'])

start_time_minutes = 540
start_location = 'North Beach'

best_schedule = None
best_num_meetings = 0
best_travel_time = float('inf')

for perm in itertools.permutations(meetings):
    current_time = start_time_minutes
    current_loc = start_location
    scheduled_meetings = []
    num_meetings = 0
    for meeting in perm:
        travel_duration = travel_times[current_loc][meeting['location']]
        current_time += travel_duration
        start_meeting = max(current_time, meeting['available_start'])
        end_meeting = start_meeting + meeting['min_duration']
        if end_meeting > meeting['available_end']:
            break
        scheduled_meetings.append({
            'person': meeting['person'],
            'location': meeting['location'],
            'start_time': start_meeting,
            'end_time': end_meeting
        })
        num_meetings += 1
        current_time = end_meeting
        current_loc = meeting['location']
    else:
        num_meetings = len(scheduled_meetings)
    
    if num_meetings > 0:
        total_travel = 0
        loc_sequence = [start_location] + [m['location'] for m in scheduled_meetings]
        for i in range(len(loc_sequence) - 1):
            total_travel += travel_times[loc_sequence[i]][loc_sequence[i+1]]
    else:
        total_travel = float('inf')
    
    if num_meetings > best_num_meetings:
        best_num_meetings = num_meetings
        best_travel_time = total_travel
        best_schedule = scheduled_meetings
    elif num_meetings == best_num_meetings and total_travel < best_travel_time:
        best_travel_time = total_travel
        best_schedule = scheduled_meetings

if best_schedule is None:
    result = {"itinerary": []}
else:
    itinerary = []
    for meet in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": meet['location'],
            "person": meet['person'],
            "start_time": minutes_to_time(meet['start_time']),
            "end_time": minutes_to_time(meet['end_time'])
        })
    result = {"itinerary": itinerary}

print(json.dumps(result))