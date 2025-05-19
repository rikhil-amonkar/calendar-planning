import itertools
import json

def time_to_min(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

friends = [
    {
        'name': 'Betty',
        'location': 'Presidio',
        'available_start': time_to_min('10:15'),
        'available_end': time_to_min('21:30'),
        'duration': 45
    },
    {
        'name': 'David',
        'location': 'Richmond District',
        'available_start': time_to_min('13:00'),
        'available_end': time_to_min('20:15'),
        'duration': 90
    },
    {
        'name': 'Barbara',
        'location': "Fisherman's Wharf",
        'available_start': time_to_min('9:15'),
        'available_end': time_to_min('20:15'),
        'duration': 120
    }
]

travel_times = {
    'Embarcadero': {'Presidio': 20, 'Richmond District': 21, "Fisherman's Wharf": 6},
    'Presidio': {'Embarcadero': 20, 'Richmond District': 7, "Fisherman's Wharf": 19},
    'Richmond District': {'Embarcadero': 19, 'Presidio': 7, "Fisherman's Wharf": 18},
    "Fisherman's Wharf": {'Embarcadero': 8, 'Presidio': 17, 'Richmond District': 18}
}

best_schedule = []
max_met = 0
min_end = float('inf')

for perm in itertools.permutations(friends):
    current_loc = 'Embarcadero'
    current_time = time_to_min('9:00')
    schedule = []
    for friend in perm:
        travel = travel_times[current_loc].get(friend['location'], 0)
        arrive = current_time + travel
        if arrive < friend['available_start']:
            arrive = friend['available_start']
        if arrive + friend['duration'] <= friend['available_end']:
            schedule.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': min_to_time(arrive),
                'end_time': min_to_time(arrive + friend['duration'])
            })
            current_time = arrive + friend['duration']
            current_loc = friend['location']
    met = len(schedule)
    end_time = current_time if met > 0 else 0
    if met > max_met or (met == max_met and end_time < min_end):
        max_met = met
        best_schedule = schedule
        min_end = end_time

print(json.dumps({'itinerary': best_schedule}, indent=2))