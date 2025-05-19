import itertools

def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h}:{m:02d}"

travel_times = {
    'Haight-Ashbury': {
        'Mission District': 11,
        'Bayview': 18,
        'Pacific Heights': 12,
        'Russian Hill': 17,
        'Fisherman\'s Wharf': 23,
    },
    'Mission District': {
        'Haight-Ashbury': 12,
        'Bayview': 15,
        'Pacific Heights': 16,
        'Russian Hill': 15,
        'Fisherman\'s Wharf': 22,
    },
    'Bayview': {
        'Haight-Ashbury': 19,
        'Mission District': 13,
        'Pacific Heights': 23,
        'Russian Hill': 23,
        'Fisherman\'s Wharf': 25,
    },
    'Pacific Heights': {
        'Haight-Ashbury': 11,
        'Mission District': 15,
        'Bayview': 22,
        'Russian Hill': 7,
        'Fisherman\'s Wharf': 13,
    },
    'Russian Hill': {
        'Haight-Ashbury': 17,
        'Mission District': 16,
        'Bayview': 23,
        'Pacific Heights': 7,
        'Fisherman\'s Wharf': 7,
    },
    'Fisherman\'s Wharf': {
        'Haight-Ashbury': 22,
        'Mission District': 22,
        'Bayview': 26,
        'Pacific Heights': 12,
        'Russian Hill': 7,
    },
}

friends = [
    {'name': 'Stephanie', 'location': 'Mission District', 'start': '8:15', 'end': '13:45', 'duration': 90},
    {'name': 'Sandra', 'location': 'Bayview', 'start': '13:00', 'end': '19:30', 'duration': 15},
    {'name': 'Richard', 'location': 'Pacific Heights', 'start': '7:15', 'end': '10:15', 'duration': 75},
    {'name': 'Brian', 'location': 'Russian Hill', 'start': '12:15', 'end': '16:00', 'duration': 120},
    {'name': 'Jason', 'location': 'Fisherman\'s Wharf', 'start': '8:30', 'end': '17:45', 'duration': 60},
]

best_itinerary = []

for perm in itertools.permutations(friends):
    current_location = 'Haight-Ashbury'
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