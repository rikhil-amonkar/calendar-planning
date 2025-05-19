import itertools

def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h}:{m:02d}"

travel_times = {
    'Mission District': {
        'The Castro': 7,
        'Nob Hill': 12,
        'Presidio': 25,
        'Marina District': 19,
        'Pacific Heights': 16,
        'Golden Gate Park': 17,
        'Chinatown': 16,
        'Richmond District': 20,
    },
    'The Castro': {
        'Mission District': 7,
        'Nob Hill': 16,
        'Presidio': 20,
        'Marina District': 21,
        'Pacific Heights': 16,
        'Golden Gate Park': 11,
        'Chinatown': 22,
        'Richmond District': 16,
    },
    'Nob Hill': {
        'Mission District': 13,
        'The Castro': 17,
        'Presidio': 17,
        'Marina District': 11,
        'Pacific Heights': 8,
        'Golden Gate Park': 17,
        'Chinatown': 6,
        'Richmond District': 14,
    },
    'Presidio': {
        'Mission District': 26,
        'The Castro': 21,
        'Nob Hill': 18,
        'Marina District': 11,
        'Pacific Heights': 11,
        'Golden Gate Park': 12,
        'Chinatown': 21,
        'Richmond District': 7,
    },
    'Marina District': {
        'Mission District': 20,
        'The Castro': 22,
        'Nob Hill': 12,
        'Presidio': 10,
        'Pacific Heights': 7,
        'Golden Gate Park': 18,
        'Chinatown': 15,
        'Richmond District': 11,
    },
    'Pacific Heights': {
        'Mission District': 15,
        'The Castro': 16,
        'Nob Hill': 8,
        'Presidio': 11,
        'Marina District': 6,
        'Golden Gate Park': 15,
        'Chinatown': 11,
        'Richmond District': 12,
    },
    'Golden Gate Park': {
        'Mission District': 17,
        'The Castro': 13,
        'Nob Hill': 20,
        'Presidio': 11,
        'Marina District': 16,
        'Pacific Heights': 16,
        'Chinatown': 23,
        'Richmond District': 7,
    },
    'Chinatown': {
        'Mission District': 17,
        'The Castro': 22,
        'Nob Hill': 9,
        'Presidio': 19,
        'Marina District': 12,
        'Pacific Heights': 10,
        'Golden Gate Park': 23,
        'Richmond District': 20,
    },
    'Richmond District': {
        'Mission District': 20,
        'The Castro': 16,
        'Nob Hill': 17,
        'Presidio': 7,
        'Marina District': 9,
        'Pacific Heights': 10,
        'Golden Gate Park': 9,
        'Chinatown': 20,
    },
}

friends = [
    {'name': 'Lisa', 'location': 'The Castro', 'start': '19:15', 'end': '21:15', 'duration': 120},
    {'name': 'Daniel', 'location': 'Nob Hill', 'start': '8:15', 'end': '11:00', 'duration': 15},
    {'name': 'Elizabeth', 'location': 'Presidio', 'start': '21:15', 'end': '22:15', 'duration': 45},
    {'name': 'Steven', 'location': 'Marina District', 'start': '16:30', 'end': '20:45', 'duration': 90},
    {'name': 'Timothy', 'location': 'Pacific Heights', 'start': '12:00', 'end': '18:00', 'duration': 90},
    {'name': 'Ashley', 'location': 'Golden Gate Park', 'start': '20:45', 'end': '21:45', 'duration': 60},
    {'name': 'Kevin', 'location': 'Chinatown', 'start': '12:00', 'end': '19:00', 'duration': 30},
    {'name': 'Betty', 'location': 'Richmond District', 'start': '13:15', 'end': '15:45', 'duration': 30},
]

best_itinerary = []

for perm in itertools.permutations(friends):
    current_location = 'Mission District'
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