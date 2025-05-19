import itertools

def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h}:{m:02d}"

travel_times = {
    'Bayview': {
        'North Beach': 21,
        'Presidio': 31,
        'Haight-Ashbury': 19,
        'Union Square': 17,
    },
    'North Beach': {
        'Bayview': 22,
        'Presidio': 17,
        'Haight-Ashbury': 18,
        'Union Square': 7,
    },
    'Presidio': {
        'Bayview': 31,
        'North Beach': 18,
        'Haight-Ashbury': 15,
        'Union Square': 22,
    },
    'Haight-Ashbury': {
        'Bayview': 18,
        'North Beach': 19,
        'Presidio': 15,
        'Union Square': 17,
    },
    'Union Square': {
        'Bayview': 15,
        'North Beach': 10,
        'Presidio': 24,
        'Haight-Ashbury': 18,
    },
}

friends = [
    {'name': 'Barbara', 'location': 'North Beach', 'start': '13:45', 'end': '20:15', 'duration': 60},
    {'name': 'Margaret', 'location': 'Presidio', 'start': '10:15', 'end': '15:15', 'duration': 30},
    {'name': 'Kevin', 'location': 'Haight-Ashbury', 'start': '20:00', 'end': '20:45', 'duration': 30},
    {'name': 'Kimberly', 'location': 'Union Square', 'start': '7:45', 'end': '16:45', 'duration': 30},
]

best_itinerary = []

for perm in itertools.permutations(friends):
    current_location = 'Bayview'
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