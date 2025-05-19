import itertools

def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h}:{m:02d}"

travel_times = {
    'Alamo Square': {
        'Russian Hill': 13,
        'Presidio': 18,
        'Chinatown': 16,
        'Sunset District': 16,
        'The Castro': 8,
        'Embarcadero': 17,
        'Golden Gate Park': 9,
    },
    'Russian Hill': {
        'Alamo Square': 15,
        'Presidio': 14,
        'Chinatown': 9,
        'Sunset District': 23,
        'The Castro': 21,
        'Embarcadero': 8,
        'Golden Gate Park': 21,
    },
    'Presidio': {
        'Alamo Square': 18,
        'Russian Hill': 14,
        'Chinatown': 21,
        'Sunset District': 15,
        'The Castro': 21,
        'Embarcadero': 20,
        'Golden Gate Park': 12,
    },
    'Chinatown': {
        'Alamo Square': 17,
        'Russian Hill': 7,
        'Presidio': 19,
        'Sunset District': 29,
        'The Castro': 22,
        'Embarcadero': 5,
        'Golden Gate Park': 23,
    },
    'Sunset District': {
        'Alamo Square': 17,
        'Russian Hill': 24,
        'Presidio': 16,
        'Chinatown': 30,
        'The Castro': 17,
        'Embarcadero': 31,
        'Golden Gate Park': 11,
    },
    'The Castro': {
        'Alamo Square': 8,
        'Russian Hill': 18,
        'Presidio': 20,
        'Chinatown': 20,
        'Sunset District': 17,
        'Embarcadero': 22,
        'Golden Gate Park': 11,
    },
    'Embarcadero': {
        'Alamo Square': 19,
        'Russian Hill': 8,
        'Presidio': 20,
        'Chinatown': 7,
        'Sunset District': 30,
        'The Castro': 25,
        'Golden Gate Park': 25,
    },
    'Golden Gate Park': {
        'Alamo Square': 10,
        'Russian Hill': 19,
        'Presidio': 11,
        'Chinatown': 23,
        'Sunset District': 10,
        'The Castro': 13,
        'Embarcadero': 25,
    },
}

friends = [
    {'name': 'Emily', 'location': 'Russian Hill', 'start': '12:15', 'end': '14:15', 'duration': 105},
    {'name': 'Mark', 'location': 'Presidio', 'start': '14:45', 'end': '19:30', 'duration': 60},
    {'name': 'Deborah', 'location': 'Chinatown', 'start': '7:30', 'end': '15:30', 'duration': 45},
    {'name': 'Margaret', 'location': 'Sunset District', 'start': '21:30', 'end': '22:30', 'duration': 60},
    {'name': 'George', 'location': 'The Castro', 'start': '7:30', 'end': '14:15', 'duration': 60},
    {'name': 'Andrew', 'location': 'Embarcadero', 'start': '20:15', 'end': '22:00', 'duration': 75},
    {'name': 'Steven', 'location': 'Golden Gate Park', 'start': '11:15', 'end': '21:15', 'duration': 105},
]

best_itinerary = []

for perm in itertools.permutations(friends):
    current_location = 'Alamo Square'
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