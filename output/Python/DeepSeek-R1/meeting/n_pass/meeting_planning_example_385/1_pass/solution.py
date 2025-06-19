import itertools
import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1]) if len(parts) > 1 else 0
    return hours * 60 + minutes

def minutes_to_time(minutes_val):
    hours = minutes_val // 60
    minutes = minutes_val % 60
    return f"{hours}:{minutes:02d}"

travel_times = {
    "Nob Hill": {
        "Nob Hill": 0,
        "Presidio": 17,
        "North Beach": 8,
        "Fisherman's Wharf": 11,
        "Pacific Heights": 8
    },
    "Presidio": {
        "Nob Hill": 18,
        "Presidio": 0,
        "North Beach": 18,
        "Fisherman's Wharf": 19,
        "Pacific Heights": 11
    },
    "North Beach": {
        "Nob Hill": 7,
        "Presidio": 17,
        "North Beach": 0,
        "Fisherman's Wharf": 5,
        "Pacific Heights": 8
    },
    "Fisherman's Wharf": {
        "Nob Hill": 11,
        "Presidio": 17,
        "North Beach": 6,
        "Fisherman's Wharf": 0,
        "Pacific Heights": 12
    },
    "Pacific Heights": {
        "Nob Hill": 8,
        "Presidio": 11,
        "North Beach": 9,
        "Fisherman's Wharf": 13,
        "Pacific Heights": 0
    }
}

friends = [
    {
        'name': 'Jeffrey',
        'location': 'Presidio',
        'start_str': '8:00',
        'end_str': '10:00',
        'min_duration': 105
    },
    {
        'name': 'John',
        'location': 'Pacific Heights',
        'start_str': '9:00',
        'end_str': '13:30',
        'min_duration': 15
    },
    {
        'name': 'Steven',
        'location': 'North Beach',
        'start_str': '13:30',
        'end_str': '22:00',
        'min_duration': 45
    },
    {
        'name': 'Barbara',
        'location': "Fisherman's Wharf",
        'start_str': '18:00',
        'end_str': '21:30',
        'min_duration': 30
    }
]

for friend in friends:
    friend['start_min'] = time_to_minutes(friend['start_str'])
    friend['end_min'] = time_to_minutes(friend['end_str'])

start_time_minutes = 540
start_location = 'Nob Hill'

best_itinerary = None
best_count = 0
best_waiting = float('inf')

for perm in itertools.permutations(friends):
    current_time = start_time_minutes
    current_location = start_location
    itinerary_perm = []
    count = 0
    total_waiting = 0
    for friend in perm:
        if current_location == friend['location']:
            travel_time = 0
        else:
            travel_time = travel_times[current_location][friend['location']]
        
        leave_time = max(current_time, friend['start_min'] - travel_time)
        wait_time_here = leave_time - current_time
        total_waiting += wait_time_here
        
        arrival_time = leave_time + travel_time
        meeting_start = max(arrival_time, friend['start_min'])
        meeting_end = meeting_start + friend['min_duration']
        
        if meeting_end <= friend['end_min']:
            itinerary_perm.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            count += 1
            current_time = meeting_end
            current_location = friend['location']
        else:
            total_waiting -= wait_time_here
    
    if count > best_count or (count == best_count and total_waiting < best_waiting):
        best_count = count
        best_itinerary = itinerary_perm
        best_waiting = total_waiting

result = {
    "itinerary": best_itinerary
}

print(json.dumps(result))