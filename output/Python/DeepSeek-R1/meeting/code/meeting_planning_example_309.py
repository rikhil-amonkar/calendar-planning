import itertools
import json

def time_to_minutes(t):
    hours, mins = map(int, t.split(':'))
    return hours * 60 + mins

def minutes_to_time(m):
    return f"{m // 60}:{m % 60:02d}"

friends = [
    {
        'name': 'Nancy',
        'location': 'Chinatown',
        'start': time_to_minutes('9:30'),
        'end': time_to_minutes('13:30'),
        'duration': 90
    },
    {
        'name': 'Mary',
        'location': 'Alamo Square',
        'start': time_to_minutes('7:00'),
        'end': time_to_minutes('21:00'),
        'duration': 75
    },
    {
        'name': 'Jessica',
        'location': 'Bayview',
        'start': time_to_minutes('11:15'),
        'end': time_to_minutes('13:45'),
        'duration': 45
    }
]

travel_times = {
    'Financial District': {'Chinatown': 5, 'Alamo Square': 17, 'Bayview': 19, 'Fisherman\'s Wharf': 10},
    'Chinatown': {'Financial District': 5, 'Alamo Square': 17, 'Bayview': 22, 'Fisherman\'s Wharf': 8},
    'Alamo Square': {'Financial District': 17, 'Chinatown': 16, 'Bayview': 16, 'Fisherman\'s Wharf': 19},
    'Bayview': {'Financial District': 19, 'Chinatown': 18, 'Alamo Square': 16, 'Fisherman\'s Wharf': 25},
    'Fisherman\'s Wharf': {'Financial District': 11, 'Chinatown': 12, 'Alamo Square': 20, 'Bayview': 26}
}

best_count = 0
best_schedule = []
current_location = 'Financial District'
start_time = time_to_minutes('9:00')

for perm in itertools.permutations(friends):
    current_loc = 'Financial District'
    current_time = start_time
    schedule = []
    count = 0
    possible = True
    for friend in perm:
        try:
            travel = travel_times[current_loc][friend['location']]
        except KeyError:
            possible = False
            break
        arrival = current_time + travel
        start = max(arrival, friend['start'])
        end = start + friend['duration']
        if end > friend['end']:
            possible = False
            break
        schedule.append((friend, start, end))
        current_time = end
        current_loc = friend['location']
        count += 1
    if possible and count > best_count or (count == best_count and current_time < sum(entry[2] for entry in best_schedule)):
        best_count = count
        best_schedule = schedule.copy()

itinerary = []
for entry in best_schedule:
    friend, start, end = entry
    itinerary.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": minutes_to_time(start).replace(':0', ':') if (start % 60) < 10 else minutes_to_time(start),
        "end_time": minutes_to_time(end).replace(':0', ':') if (end % 60) < 10 else minutes_to_time(end)
    })

print(json.dumps({"itinerary": itinerary}, indent=2))