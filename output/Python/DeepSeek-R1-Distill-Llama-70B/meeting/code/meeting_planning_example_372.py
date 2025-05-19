import itertools

def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h}:{m:02d}"

travel_times = {
    'Sunset District': {
        'Alamo Square': 17,
        'Russian Hill': 24,
        'Golden Gate Park': 11,
        'Mission District': 24,
    },
    'Alamo Square': {
        'Sunset District': 16,
        'Russian Hill': 13,
        'Golden Gate Park': 9,
        'Mission District': 10,
    },
    'Russian Hill': {
        'Sunset District': 23,
        'Alamo Square': 15,
        'Golden Gate Park': 21,
        'Mission District': 16,
    },
    'Golden Gate Park': {
        'Sunset District': 10,
        'Alamo Square': 10,
        'Russian Hill': 19,
        'Mission District': 17,
    },
    'Mission District': {
        'Sunset District': 24,
        'Alamo Square': 11,
        'Russian Hill': 15,
        'Golden Gate Park': 17,
    },
}

friends = [
    {'name': 'Charles', 'location': 'Alamo Square', 'start': '18:00', 'end': '20:45', 'duration': 90},
    {'name': 'Margaret', 'location': 'Russian Hill', 'start': '9:00', 'end': '16:00', 'duration': 30},
    {'name': 'Daniel', 'location': 'Golden Gate Park', 'start': '8:00', 'end': '13:30', 'duration': 15},
    {'name': 'Stephanie', 'location': 'Mission District', 'start': '20:30', 'end': '22:00', 'duration': 90},
]

best_itinerary = []

for perm in itertools.permutations(friends):
    current_location = 'Sunset District'
    current_time = 540  # 9:00 AM
    itinerary = []
    valid = True
    for friend in perm:
        travel = travel_times[current_location][friend['location']]
        arrival = current_time + travel
        start = time_to_minutes(friend['start'])
        end = time_to_minutes(friend['end'])
        meet_start = max(arrival, start)
        meet_end = meet_start + friend['duration']
        if meet_end > end:
            valid = False
            break
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(meet_start),
            'end_time': minutes_to_time(meet_end)
        })
        current_location = friend['location']
        current_time = meet_end
    if valid:
        if len(itinerary) > len(best_itinerary):
            best_itinerary = itinerary.copy()

print('SOLUTION:')
print('{ "itinerary": [')
for i, meeting in enumerate(best_itinerary):
    print(f'    {{"action": "meet", "location": "{meeting["location"]}", "person": "{meeting["person"]}", "start_time": "{meeting["start_time"]}", "end_time": "{meeting["end_time"]}"}}' + ('' if i == len(best_itinerary)-1 else ','))
print(']}')