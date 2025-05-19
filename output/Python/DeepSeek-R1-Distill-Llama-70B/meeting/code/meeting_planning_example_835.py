import itertools

def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h}:{m:02d}"

travel_times = {
    'Pacific Heights': {
        'Golden Gate Park': 15,
        'The Castro': 16,
        'Bayview': 22,
        'Marina District': 6,
        'Union Square': 12,
        'Sunset District': 21,
        'Alamo Square': 10,
        'Financial District': 13,
        'Mission District': 15,
    },
    'Golden Gate Park': {
        'Pacific Heights': 16,
        'The Castro': 13,
        'Bayview': 23,
        'Marina District': 16,
        'Union Square': 22,
        'Sunset District': 10,
        'Alamo Square': 9,
        'Financial District': 26,
        'Mission District': 17,
    },
    'The Castro': {
        'Pacific Heights': 16,
        'Golden Gate Park': 11,
        'Bayview': 19,
        'Marina District': 21,
        'Union Square': 19,
        'Sunset District': 17,
        'Alamo Square': 8,
        'Financial District': 21,
        'Mission District': 7,
    },
    'Bayview': {
        'Pacific Heights': 23,
        'Golden Gate Park': 22,
        'The Castro': 19,
        'Marina District': 27,
        'Union Square': 18,
        'Sunset District': 23,
        'Alamo Square': 16,
        'Financial District': 19,
        'Mission District': 13,
    },
    'Marina District': {
        'Pacific Heights': 7,
        'Golden Gate Park': 18,
        'The Castro': 22,
        'Bayview': 27,
        'Union Square': 16,
        'Sunset District': 19,
        'Alamo Square': 15,
        'Financial District': 17,
        'Mission District': 20,
    },
    'Union Square': {
        'Pacific Heights': 15,
        'Golden Gate Park': 22,
        'The Castro': 17,
        'Bayview': 15,
        'Marina District': 18,
        'Sunset District': 27,
        'Alamo Square': 15,
        'Financial District': 9,
        'Mission District': 14,
    },
    'Sunset District': {
        'Pacific Heights': 21,
        'Golden Gate Park': 11,
        'The Castro': 17,
        'Bayview': 22,
        'Marina District': 21,
        'Union Square': 30,
        'Alamo Square': 17,
        'Financial District': 30,
        'Mission District': 25,
    },
    'Alamo Square': {
        'Pacific Heights': 10,
        'Golden Gate Park': 9,
        'The Castro': 8,
        'Bayview': 16,
        'Marina District': 15,
        'Union Square': 14,
        'Sunset District': 16,
        'Financial District': 17,
        'Mission District': 10,
    },
    'Financial District': {
        'Pacific Heights': 13,
        'Golden Gate Park': 23,
        'The Castro': 20,
        'Bayview': 19,
        'Marina District': 15,
        'Union Square': 9,
        'Sunset District': 30,
        'Alamo Square': 17,
        'Mission District': 17,
    },
    'Mission District': {
        'Pacific Heights': 16,
        'Golden Gate Park': 17,
        'The Castro': 7,
        'Bayview': 14,
        'Marina District': 19,
        'Union Square': 15,
        'Sunset District': 24,
        'Alamo Square': 11,
        'Financial District': 15,
    },
}

friends = [
    {'name': 'Helen', 'location': 'Golden Gate Park', 'start': '9:30', 'end': '12:15', 'duration': 45},
    {'name': 'Steven', 'location': 'The Castro', 'start': '20:15', 'end': '22:00', 'duration': 105},
    {'name': 'Deborah', 'location': 'Bayview', 'start': '8:30', 'end': '12:00', 'duration': 30},
    {'name': 'Matthew', 'location': 'Marina District', 'start': '9:15', 'end': '14:15', 'duration': 45},
    {'name': 'Joseph', 'location': 'Union Square', 'start': '14:15', 'end': '18:45', 'duration': 120},
    {'name': 'Ronald', 'location': 'Sunset District', 'start': '16:00', 'end': '20:45', 'duration': 60},
    {'name': 'Robert', 'location': 'Alamo Square', 'start': '18:30', 'end': '21:15', 'duration': 120},
    {'name': 'Rebecca', 'location': 'Financial District', 'start': '14:45', 'end': '16:15', 'duration': 30},
    {'name': 'Elizabeth', 'location': 'Mission District', 'start': '18:30', 'end': '21:00', 'duration': 120},
]

best_itinerary = []

for perm in itertools.permutations(friends):
    current_location = 'Pacific Heights'
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