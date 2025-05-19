import itertools

def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h}:{m:02d}"

travel_times = {
    'Financial District': {
        'Golden Gate Park': 23,
        'Chinatown': 5,
        'Union Square': 9,
        'Fisherman\'s Wharf': 10,
        'Pacific Heights': 13,
        'North Beach': 7,
    },
    'Golden Gate Park': {
        'Financial District': 26,
        'Chinatown': 23,
        'Union Square': 22,
        'Fisherman\'s Wharf': 24,
        'Pacific Heights': 16,
        'North Beach': 24,
    },
    'Chinatown': {
        'Financial District': 5,
        'Golden Gate Park': 23,
        'Union Square': 7,
        'Fisherman\'s Wharf': 8,
        'Pacific Heights': 10,
        'North Beach': 3,
    },
    'Union Square': {
        'Financial District': 9,
        'Golden Gate Park': 22,
        'Chinatown': 7,
        'Fisherman\'s Wharf': 15,
        'Pacific Heights': 15,
        'North Beach': 10,
    },
    'Fisherman\'s Wharf': {
        'Financial District': 11,
        'Golden Gate Park': 25,
        'Chinatown': 12,
        'Union Square': 13,
        'Pacific Heights': 12,
        'North Beach': 6,
    },
    'Pacific Heights': {
        'Financial District': 13,
        'Golden Gate Park': 15,
        'Chinatown': 11,
        'Union Square': 12,
        'Fisherman\'s Wharf': 13,
        'North Beach': 9,
    },
    'North Beach': {
        'Financial District': 8,
        'Golden Gate Park': 22,
        'Chinatown': 6,
        'Union Square': 7,
        'Fisherman\'s Wharf': 5,
        'Pacific Heights': 8,
    },
}

friends = [
    {'name': 'Stephanie', 'location': 'Golden Gate Park', 'start': '11:00', 'end': '15:00', 'duration': 105},
    {'name': 'Karen', 'location': 'Chinatown', 'start': '13:45', 'end': '16:30', 'duration': 15},
    {'name': 'Brian', 'location': 'Union Square', 'start': '15:00', 'end': '17:15', 'duration': 30},
    {'name': 'Rebecca', 'location': 'Fisherman\'s Wharf', 'start': '8:00', 'end': '11:15', 'duration': 30},
    {'name': 'Joseph', 'location': 'Pacific Heights', 'start': '8:15', 'end': '9:30', 'duration': 60},
    {'name': 'Steven', 'location': 'North Beach', 'start': '14:30', 'end': '20:45', 'duration': 120},
]

best_itinerary = []

for perm in itertools.permutations(friends):
    current_location = 'Financial District'
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