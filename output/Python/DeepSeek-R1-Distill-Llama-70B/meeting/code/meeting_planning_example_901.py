import itertools

def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h}:{m:02d}"

travel_times = {
    'Russian Hill': {
        'Pacific Heights': 7,
        'North Beach': 5,
        'Golden Gate Park': 21,
        'Embarcadero': 8,
        'Haight-Ashbury': 17,
        'Fisherman\'s Wharf': 7,
        'Mission District': 16,
        'Alamo Square': 15,
        'Bayview': 23,
        'Richmond District': 14,
    },
    'Pacific Heights': {
        'Russian Hill': 7,
        'North Beach': 9,
        'Golden Gate Park': 15,
        'Embarcadero': 10,
        'Haight-Ashbury': 11,
        'Fisherman\'s Wharf': 13,
        'Mission District': 15,
        'Alamo Square': 10,
        'Bayview': 22,
        'Richmond District': 12,
    },
    'North Beach': {
        'Russian Hill': 4,
        'Pacific Heights': 8,
        'Golden Gate Park': 22,
        'Embarcadero': 6,
        'Haight-Ashbury': 18,
        'Fisherman\'s Wharf': 5,
        'Mission District': 18,
        'Alamo Square': 16,
        'Bayview': 25,
        'Richmond District': 18,
    },
    'Golden Gate Park': {
        'Russian Hill': 19,
        'Pacific Heights': 16,
        'North Beach': 23,
        'Embarcadero': 25,
        'Haight-Ashbury': 7,
        'Fisherman\'s Wharf': 24,
        'Mission District': 17,
        'Alamo Square': 9,
        'Bayview': 23,
        'Richmond District': 7,
    },
    'Embarcadero': {
        'Russian Hill': 8,
        'Pacific Heights': 11,
        'North Beach': 5,
        'Golden Gate Park': 25,
        'Haight-Ashbury': 21,
        'Fisherman\'s Wharf': 6,
        'Mission District': 20,
        'Alamo Square': 19,
        'Bayview': 21,
        'Richmond District': 21,
    },
    'Haight-Ashbury': {
        'Russian Hill': 17,
        'Pacific Heights': 12,
        'North Beach': 19,
        'Golden Gate Park': 7,
        'Embarcadero': 20,
        'Fisherman\'s Wharf': 23,
        'Mission District': 11,
        'Alamo Square': 5,
        'Bayview': 18,
        'Richmond District': 10,
    },
    'Fisherman\'s Wharf': {
        'Russian Hill': 7,
        'Pacific Heights': 12,
        'North Beach': 6,
        'Golden Gate Park': 25,
        'Embarcadero': 8,
        'Haight-Ashbury': 22,
        'Mission District': 22,
        'Alamo Square': 21,
        'Bayview': 26,
        'Richmond District': 18,
    },
    'Mission District': {
        'Russian Hill': 15,
        'Pacific Heights': 16,
        'North Beach': 17,
        'Golden Gate Park': 17,
        'Embarcadero': 19,
        'Haight-Ashbury': 12,
        'Fisherman\'s Wharf': 22,
        'Alamo Square': 11,
        'Bayview': 14,
        'Richmond District': 20,
    },
    'Alamo Square': {
        'Russian Hill': 13,
        'Pacific Heights': 10,
        'North Beach': 15,
        'Golden Gate Park': 9,
        'Embarcadero': 16,
        'Haight-Ashbury': 5,
        'Fisherman\'s Wharf': 19,
        'Mission District': 10,
        'Bayview': 16,
        'Richmond District': 11,
    },
    'Bayview': {
        'Russian Hill': 23,
        'Pacific Heights': 23,
        'North Beach': 22,
        'Golden Gate Park': 22,
        'Embarcadero': 19,
        'Haight-Ashbury': 19,
        'Fisherman\'s Wharf': 25,
        'Mission District': 13,
        'Alamo Square': 16,
        'Richmond District': 25,
    },
    'Richmond District': {
        'Russian Hill': 13,
        'Pacific Heights': 10,
        'North Beach': 17,
        'Golden Gate Park': 9,
        'Embarcadero': 19,
        'Haight-Ashbury': 10,
        'Fisherman\'s Wharf': 18,
        'Mission District': 20,
        'Alamo Square': 13,
        'Bayview': 27,
    },
}

friends = [
    {'name': 'Emily', 'location': 'Pacific Heights', 'start': '9:15', 'end': '13:45', 'duration': 120},
    {'name': 'Helen', 'location': 'North Beach', 'start': '13:45', 'end': '18:45', 'duration': 30},
    {'name': 'Kimberly', 'location': 'Golden Gate Park', 'start': '18:45', 'end': '21:15', 'duration': 75},
    {'name': 'James', 'location': 'Embarcadero', 'start': '10:30', 'end': '11:30', 'duration': 30},
    {'name': 'Linda', 'location': 'Haight-Ashbury', 'start': '7:30', 'end': '19:15', 'duration': 15},
    {'name': 'Paul', 'location': 'Fisherman\'s Wharf', 'start': '14:45', 'end': '18:45', 'duration': 90},
    {'name': 'Anthony', 'location': 'Mission District', 'start': '8:00', 'end': '14:45', 'duration': 105},
    {'name': 'Nancy', 'location': 'Alamo Square', 'start': '8:30', 'end': '13:45', 'duration': 120},
    {'name': 'William', 'location': 'Bayview', 'start': '17:30', 'end': '20:30', 'duration': 120},
    {'name': 'Margaret', 'location': 'Richmond District', 'start': '15:15', 'end': '18:15', 'duration': 45},
]

best_itinerary = []

for perm in itertools.permutations(friends):
    current_location = 'Russian Hill'
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