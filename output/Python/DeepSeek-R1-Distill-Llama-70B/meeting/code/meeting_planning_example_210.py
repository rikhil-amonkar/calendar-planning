import itertools

def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h}:{m:02d}"

travel_times = {
    'Fisherman\'s Wharf': {
        'Presidio': 17,
        'Richmond District': 18,
        'Financial District': 11,
    },
    'Presidio': {
        'Fisherman\'s Wharf': 19,
        'Richmond District': 7,
        'Financial District': 23,
    },
    'Richmond District': {
        'Fisherman\'s Wharf': 18,
        'Presidio': 7,
        'Financial District': 22,
    },
    'Financial District': {
        'Fisherman\'s Wharf': 10,
        'Presidio': 22,
        'Richmond District': 21,
    },
}

friends = [
    {'name': 'Emily', 'location': 'Presidio', 'start': '16:15', 'end': '21:00', 'duration': 105},
    {'name': 'Joseph', 'location': 'Richmond District', 'start': '17:15', 'end': '22:00', 'duration': 120},
    {'name': 'Melissa', 'location': 'Financial District', 'start': '15:45', 'end': '21:45', 'duration': 75},
]

best_itinerary = []

for perm in itertools.permutations(friends):
    current_location = 'Fisherman\'s Wharf'
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