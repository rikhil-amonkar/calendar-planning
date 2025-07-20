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

travel_time = {
    'Pacific Heights': {
        'North Beach': 9,
        'Financial District': 13,
        'Alamo Square': 10,
        'Mission District': 15
    },
    'North Beach': {
        'Pacific Heights': 8,
        'Financial District': 8,
        'Alamo Square': 16,
        'Mission District': 18
    },
    'Financial District': {
        'Pacific Heights': 13,
        'North Beach': 7,
        'Alamo Square': 17,
        'Mission District': 17
    },
    'Alamo Square': {
        'Pacific Heights': 10,
        'North Beach': 15,
        'Financial District': 17,
        'Mission District': 10
    },
    'Mission District': {
        'Pacific Heights': 16,
        'North Beach': 17,
        'Financial District': 17,
        'Alamo Square': 11
    }
}

friends = [
    {
        'name': 'Helen',
        'location': 'North Beach',
        'start': '9:00',
        'end': '17:00',
        'min_duration': 15
    },
    {
        'name': 'Betty',
        'location': 'Financial District',
        'start': '19:00',
        'end': '21:45',
        'min_duration': 90
    },
    {
        'name': 'Amanda',
        'location': 'Alamo Square',
        'start': '19:45',
        'end': '21:00',
        'min_duration': 60
    },
    {
        'name': 'Kevin',
        'location': 'Mission District',
        'start': '10:45',
        'end': '14:45',
        'min_duration': 45
    }
]

for f in friends:
    f['available_start'] = time_to_minutes(f['start'])
    f['available_end'] = time_to_minutes(f['end'])

start_time = time_to_minutes('9:00')
start_location = 'Pacific Heights'

best_count = 0
best_schedule = None

for perm in itertools.permutations(friends):
    current_time = start_time
    current_location = start_location
    scheduled_meetings = []
    
    for friend in perm:
        if current_location == friend['location']:
            travel_duration = 0
        else:
            travel_duration = travel_time[current_location][friend['location']]
        current_time += travel_duration
        
        if current_time < friend['available_start']:
            current_time = friend['available_start']
        
        if current_time + friend['min_duration'] <= friend['available_end']:
            meeting_start = current_time
            meeting_end = current_time + friend['min_duration']
            scheduled_meetings.append({
                'name': friend['name'],
                'location': friend['location'],
                'start': meeting_start,
                'end': meeting_end
            })
            current_time = meeting_end
            current_location = friend['location']
    
    count = len(scheduled_meetings)
    if count > best_count:
        best_count = count
        best_schedule = scheduled_meetings

itinerary = []
if best_schedule is not None:
    for meeting in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['name'],
            "start_time": minutes_to_time(meeting['start']),
            "end_time": minutes_to_time(meeting['end'])
        })

result = {
    "itinerary": itinerary
}

print(json.dumps(result))