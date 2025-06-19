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

start_time_minutes = 540  # 9:00 in minutes
start_location = 'North Beach'

best_schedule = None
best_num_meetings = 0
best_travel_time = float('inf')

for perm in itertools.permutations(meetings):
    current_time = start_time_minutes
    current_loc = start_location
    scheduled_meetings = []
    valid = True
    for idx, meeting in enumerate(perm):
        # Travel to the meeting location
        travel_duration = travel_times[current_loc][meeting['location']]
        current_time += travel_duration  # arrival time at meeting location
        
        # Determine meeting start time (can't start before available time)
        start_meeting = max(current_time, meeting['available_start'])
        # Check if meeting can be scheduled with minimum duration without exceeding available_end
        if start_meeting + meeting['min_duration'] > meeting['available_end']:
            valid = False
            break
            
        # If not last meeting, check if we can leave in time for next meeting
        if idx < len(perm) - 1:
            next_meeting = perm[idx+1]
            travel_next = travel_times[meeting['location']][next_meeting['location']]
            # Latest departure time to make next meeting
            latest_departure = next_meeting['available_end'] - next_meeting['min_duration'] - travel_next
            if start_meeting + meeting['min_duration'] > latest_departure:
                valid = False
                break
                
        # Schedule meeting for exactly the minimum duration
        scheduled_meetings.append({
            'person': meeting['person'],
            'location': meeting['location'],
            'start_time': start_meeting,
            'end_time': start_meeting + meeting['min_duration']
        })
        # Update current time and location
        current_time = start_meeting + meeting['min_duration']
        current_loc = meeting['location']
    
    if not valid:
        continue
        
    num_meetings = len(scheduled_meetings)
    if num_meetings == 0:
        continue
        
    # Calculate total travel time for this schedule
    total_travel = 0
    loc_sequence = [start_location] + [m['location'] for m in scheduled_meetings]
    for i in range(len(loc_sequence) - 1):
        total_travel += travel_times[loc_sequence[i]][loc_sequence[i+1]]
    
    # Update best schedule
    if num_meetings > best_num_meetings:
        best_num_meetings = num_meetings
        best_travel_time = total_travel
        best_schedule = scheduled_meetings
    elif num_meetings == best_num_meetings and total_travel < best_travel_time:
        best_travel_time = total_travel
        best_schedule = scheduled_meetings

# Format the result
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