import json

def time_to_minutes(t):
    hours, mins = map(int, t.split(':'))
    return hours * 60 + mins

def minutes_to_time(m):
    return f"{m // 60}:{m % 60:02d}".replace(":0", ":") if m % 60 != 0 else f"{m // 60}:00"

travel_times = {
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Chinatown'): 20,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Chinatown'): 16,
    ('Union Square', 'The Castro'): 19,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Chinatown'): 7,
    ('Chinatown', 'The Castro'): 22,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Union Square'): 7,
}

friends = [
    {
        'name': 'Emily',
        'location': 'Alamo Square',
        'available_start': time_to_minutes('11:45'),
        'available_end': time_to_minutes('15:15'),
        'duration': 105
    },
    {
        'name': 'Barbara',
        'location': 'Union Square',
        'available_start': time_to_minutes('16:45'),
        'available_end': time_to_minutes('18:15'),
        'duration': 60
    },
    {
        'name': 'William',
        'location': 'Chinatown',
        'available_start': time_to_minutes('17:15'),
        'available_end': time_to_minutes('19:00'),
        'duration': 105
    }
]

current_location = 'The Castro'
current_time = time_to_minutes('9:00')
itinerary = []

# Meet Emily first
emily = [f for f in friends if f['name'] == 'Emily'][0]
travel = travel_times[(current_location, emily['location'])]
arrival_time = current_time + travel
start_time = max(emily['available_start'], arrival_time)
end_time = start_time + emily['duration']
if end_time > emily['available_end']:
    start_time = emily['available_end'] - emily['duration']
    end_time = emily['available_end']
itinerary.append({
    'action': 'meet',
    'location': emily['location'],
    'person': emily['name'],
    'start_time': minutes_to_time(start_time),
    'end_time': minutes_to_time(end_time)
})
current_time = end_time
current_location = emily['location']

# Determine next possible meetings
best_meeting = None
max_duration = 0
for friend in [f for f in friends if f['name'] != 'Emily']:
    travel_time = travel_times.get((current_location, friend['location']), float('inf'))
    arrival = current_time + travel_time
    start = max(arrival, friend['available_start'])
    end = start + friend['duration']
    if end <= friend['available_end'] and friend['duration'] > max_duration:
        best_meeting = friend
        best_start = start
        best_end = end
        max_duration = friend['duration']

if best_meeting:
    itinerary.append({
        'action': 'meet',
        'location': best_meeting['location'],
        'person': best_meeting['name'],
        'start_time': minutes_to_time(best_start),
        'end_time': minutes_to_time(best_end)
    })

print(json.dumps({"itinerary": itinerary}, indent=2))