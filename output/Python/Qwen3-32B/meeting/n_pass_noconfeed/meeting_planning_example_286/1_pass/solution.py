import itertools
import json

def time_str_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

travel_times = {
    'Union Square': {
        'Mission District': 14,
        'Bayview': 15,
        'Sunset District': 26
    },
    'Mission District': {
        'Union Square': 15,
        'Bayview': 15,
        'Sunset District': 24
    },
    'Bayview': {
        'Union Square': 17,
        'Mission District': 13,
        'Sunset District': 23
    },
    'Sunset District': {
        'Union Square': 30,
        'Mission District': 24,
        'Bayview': 22
    }
}

friends = [
    {
        'name': 'Carol',
        'location': 'Sunset District',
        'available_start': '10:15',
        'available_end': '11:45',
        'required_duration': 30
    },
    {
        'name': 'Karen',
        'location': 'Bayview',
        'available_start': '12:45',
        'available_end': '15:00',
        'required_duration': 120
    },
    {
        'name': 'Rebecca',
        'location': 'Mission District',
        'available_start': '11:30',
        'available_end': '20:15',
        'required_duration': 120
    }
]

best_schedule = []
max_meetings = 0

for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM in minutes
    current_location = 'Union Square'
    schedule = []
    valid = True
    for friend in perm:
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        
        available_start = time_str_to_minutes(friend['available_start'])
        available_end = time_str_to_minutes(friend['available_end'])
        
        start_time = max(arrival_time, available_start)
        end_time = start_time + friend['required_duration']
        
        if end_time > available_end:
            valid = False
            break
        
        schedule.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time_str(start_time),
            'end_time': minutes_to_time_str(end_time)
        })
        
        current_time = end_time
        current_location = friend['location']
    
    if valid and len(schedule) > max_meetings:
        max_meetings = len(schedule)
        best_schedule = schedule

result = {"itinerary": best_schedule}
print(json.dumps(result, indent=2))