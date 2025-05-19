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
        'North Beach': 29,
        'Union Square': 30,
        'Alamo Square': 17,
    },
    'North Beach': {
        'Sunset District': 27,
        'Union Square': 7,
        'Alamo Square': 16,
    },
    'Union Square': {
        'Sunset District': 26,
        'North Beach': 10,
        'Alamo Square': 15,
    },
    'Alamo Square': {
        'Sunset District': 16,
        'North Beach': 15,
        'Union Square': 14,
    },
}

friends = [
    {'name': 'Sarah', 'location': 'North Beach', 'start': '16:00', 'end': '18:15', 'duration': 60},
    {'name': 'Jeffrey', 'location': 'Union Square', 'start': '15:00', 'end': '22:00', 'duration': 75},
    {'name': 'Brian', 'location': 'Alamo Square', 'start': '16:00', 'end': '17:30', 'duration': 75},
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