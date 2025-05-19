import itertools

def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h}:{m:02d}"

travel_times = {
    'The Castro': {
        'Marina District': 21,
        'Presidio': 20,
        'North Beach': 20,
        'Embarcadero': 22,
        'Haight-Ashbury': 6,
        'Golden Gate Park': 11,
        'Richmond District': 16,
        'Alamo Square': 8,
        'Financial District': 21,
        'Sunset District': 17,
    },
    'Marina District': {
        'The Castro': 22,
        'Presidio': 10,
        'North Beach': 11,
        'Embarcadero': 14,
        'Haight-Ashbury': 16,
        'Golden Gate Park': 18,
        'Richmond District': 11,
        'Alamo Square': 15,
        'Financial District': 17,
        'Sunset District': 19,
    },
    'Presidio': {
        'The Castro': 21,
        'Marina District': 11,
        'North Beach': 18,
        'Embarcadero': 20,
        'Haight-Ashbury': 15,
        'Golden Gate Park': 12,
        'Richmond District': 7,
        'Alamo Square': 19,
        'Financial District': 23,
        'Sunset District': 15,
    },
    'North Beach': {
        'The Castro': 23,
        'Marina District': 9,
        'Presidio': 17,
        'Embarcadero': 6,
        'Haight-Ashbury': 18,
        'Golden Gate Park': 22,
        'Richmond District': 18,
        'Alamo Square': 16,
        'Financial District': 8,
        'Sunset District': 27,
    },
    'Embarcadero': {
        'The Castro': 25,
        'Marina District': 12,
        'Presidio': 20,
        'North Beach': 5,
        'Haight-Ashbury': 21,
        'Golden Gate Park': 25,
        'Richmond District': 21,
        'Alamo Square': 19,
        'Financial District': 5,
        'Sunset District': 30,
    },
    'Haight-Ashbury': {
        'The Castro': 6,
        'Marina District': 17,
        'Presidio': 15,
        'North Beach': 19,
        'Embarcadero': 20,
        'Golden Gate Park': 7,
        'Richmond District': 10,
        'Alamo Square': 5,
        'Financial District': 21,
        'Sunset District': 15,
    },
    'Golden Gate Park': {
        'The Castro': 13,
        'Marina District': 16,
        'Presidio': 11,
        'North Beach': 23,
        'Embarcadero': 25,
        'Haight-Ashbury': 7,
        'Richmond District': 7,
        'Alamo Square': 9,
        'Financial District': 26,
        'Sunset District': 10,
    },
    'Richmond District': {
        'The Castro': 16,
        'Marina District': 9,
        'Presidio': 7,
        'North Beach': 17,
        'Embarcadero': 19,
        'Haight-Ashbury': 10,
        'Golden Gate Park': 9,
        'Alamo Square': 13,
        'Financial District': 22,
        'Sunset District': 11,
    },
    'Alamo Square': {
        'The Castro': 8,
        'Marina District': 15,
        'Presidio': 17,
        'North Beach': 15,
        'Embarcadero': 16,
        'Haight-Ashbury': 5,
        'Golden Gate Park': 9,
        'Richmond District': 11,
        'Financial District': 17,
        'Sunset District': 16,
    },
    'Financial District': {
        'The Castro': 20,
        'Marina District': 15,
        'Presidio': 22,
        'North Beach': 7,
        'Embarcadero': 4,
        'Haight-Ashbury': 19,
        'Golden Gate Park': 23,
        'Richmond District': 21,
        'Alamo Square': 17,
        'Sunset District': 30,
    },
    'Sunset District': {
        'The Castro': 17,
        'Marina District': 21,
        'Presidio': 16,
        'North Beach': 28,
        'Embarcadero': 30,
        'Haight-Ashbury': 15,
        'Golden Gate Park': 11,
        'Richmond District': 12,
        'Alamo Square': 17,
        'Financial District': 30,
    },
}

friends = [
    {'name': 'Elizabeth', 'location': 'Marina District', 'start': '19:00', 'end': '20:45', 'duration': 105},
    {'name': 'Joshua', 'location': 'Presidio', 'start': '8:30', 'end': '13:15', 'duration': 105},
    {'name': 'Timothy', 'location': 'North Beach', 'start': '19:45', 'end': '22:00', 'duration': 90},
    {'name': 'David', 'location': 'Embarcadero', 'start': '10:45', 'end': '12:30', 'duration': 30},
    {'name': 'Kimberly', 'location': 'Haight-Ashbury', 'start': '16:45', 'end': '21:30', 'duration': 75},
    {'name': 'Lisa', 'location': 'Golden Gate Park', 'start': '17:30', 'end': '21:45', 'duration': 45},
    {'name': 'Ronald', 'location': 'Richmond District', 'start': '8:00', 'end': '9:30', 'duration': 90},
    {'name': 'Stephanie', 'location': 'Alamo Square', 'start': '15:30', 'end': '16:30', 'duration': 30},
    {'name': 'Helen', 'location': 'Financial District', 'start': '17:30', 'end': '18:30', 'duration': 45},
    {'name': 'Laura', 'location': 'Sunset District', 'start': '17:45', 'end': '21:15', 'duration': 90},
]

best_itinerary = []

for perm in itertools.permutations(friends):
    current_location = 'The Castro'
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