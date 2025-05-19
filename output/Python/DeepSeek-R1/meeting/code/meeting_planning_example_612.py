import json
from itertools import permutations

def time_to_min(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time(m):
    return f"{m // 60}:{m % 60:02d}"

friends = [
    {'name': 'Emily', 'location': 'Russian Hill', 'start': time_to_min('12:15'), 'end': time_to_min('14:15'), 'duration': 105},
    {'name': 'Mark', 'location': 'Presidio', 'start': time_to_min('14:45'), 'end': time_to_min('19:30'), 'duration': 60},
    {'name': 'Deborah', 'location': 'Chinatown', 'start': time_to_min('7:30'), 'end': time_to_min('15:30'), 'duration': 45},
    {'name': 'Margaret', 'location': 'Sunset District', 'start': time_to_min('21:30'), 'end': time_to_min('22:30'), 'duration': 60},
    {'name': 'George', 'location': 'The Castro', 'start': time_to_min('7:30'), 'end': time_to_min('14:15'), 'duration': 60},
    {'name': 'Andrew', 'location': 'Embarcadero', 'start': time_to_min('20:15'), 'end': time_to_min('22:00'), 'duration': 75},
    {'name': 'Steven', 'location': 'Golden Gate Park', 'start': time_to_min('11:15'), 'end': time_to_min('21:15'), 'duration': 105}
]

travel_times = {
    'Alamo Square': {'Russian Hill':13, 'Presidio':18, 'Chinatown':16, 'Sunset District':16, 'The Castro':8, 'Embarcadero':17, 'Golden Gate Park':9},
    'Russian Hill': {'Alamo Square':15, 'Presidio':14, 'Chinatown':9, 'Sunset District':23, 'The Castro':21, 'Embarcadero':8, 'Golden Gate Park':21},
    'Presidio': {'Alamo Square':18, 'Russian Hill':14, 'Chinatown':21, 'Sunset District':15, 'The Castro':21, 'Embarcadero':20, 'Golden Gate Park':12},
    'Chinatown': {'Alamo Square':17, 'Russian Hill':7, 'Presidio':19, 'Sunset District':29, 'The Castro':22, 'Embarcadero':5, 'Golden Gate Park':23},
    'Sunset District': {'Alamo Square':17, 'Russian Hill':24, 'Presidio':16, 'Chinatown':30, 'The Castro':17, 'Embarcadero':31, 'Golden Gate Park':11},
    'The Castro': {'Alamo Square':8, 'Russian Hill':18, 'Presidio':20, 'Chinatown':20, 'Sunset District':17, 'Embarcadero':22, 'Golden Gate Park':11},
    'Embarcadero': {'Alamo Square':19, 'Russian Hill':8, 'Presidio':20, 'Chinatown':7, 'Sunset District':30, 'The Castro':25, 'Golden Gate Park':25},
    'Golden Gate Park': {'Alamo Square':10, 'Russian Hill':19, 'Presidio':11, 'Chinatown':23, 'Sunset District':10, 'The Castro':13, 'Embarcadero':25}
}

def calculate_schedule(order):
    current_loc = 'Alamo Square'
    current_time = time_to_min('9:00')
    schedule = []
    for friend in order:
        travel = travel_times[current_loc].get(friend['location'], 0)
        arrive = current_time + travel
        start = max(arrive, friend['start'])
        if start + friend['duration'] > friend['end']:
            return None
        end = start + friend['duration']
        schedule.append((friend, start, end))
        current_loc = friend['location']
        current_time = end
    return schedule

best = []
max_count = 0

for perm in permutations(friends):
    if len(perm) < len(friends):
        continue
    valid = True
    for f in perm:
        if f['name'] == 'Margaret' and len(perm) > perm.index(f) + 1:
            valid = False
            break
    if not valid:
        continue
    schedule = calculate_schedule(perm)
    if schedule:
        count = len(schedule)
        if count > max_count or (count == max_count and schedule[-1][2] < best[-1][2]):
            max_count = count
            best = schedule

itinerary = []
current_loc = 'Alamo Square'
current_time = time_to_min('9:00')
for entry in best:
    friend, start, end = entry
    travel = travel_times[current_loc][friend['location']]
    itinerary.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": min_to_time(start),
        "end_time": min_to_time(end)
    })
    current_loc = friend['location']
    current_time = end

print(json.dumps({"itinerary": itinerary}, indent=None))