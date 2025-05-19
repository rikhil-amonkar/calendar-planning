import itertools
import json

def time_to_minutes(t):
    hours, mins = map(int, t.split(':'))
    return hours * 60 + mins

def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    'Nob Hill': {
        'Presidio': 17,
        'North Beach': 8,
        'Fisherman\'s Wharf': 11,
        'Pacific Heights': 8
    },
    'Presidio': {
        'Nob Hill': 18,
        'North Beach': 18,
        'Fisherman\'s Wharf': 19,
        'Pacific Heights': 11
    },
    'North Beach': {
        'Nob Hill': 7,
        'Presidio': 17,
        'Fisherman\'s Wharf': 5,
        'Pacific Heights': 8
    },
    'Fisherman\'s Wharf': {
        'Nob Hill': 11,
        'Presidio': 17,
        'North Beach': 6,
        'Pacific Heights': 12
    },
    'Pacific Heights': {
        'Nob Hill': 8,
        'Presidio': 11,
        'North Beach': 9,
        'Fisherman\'s Wharf': 13
    }
}

friends = [
    {'name': 'John', 'location': 'Pacific Heights', 'start': time_to_minutes('9:00'), 'end': time_to_minutes('13:30'), 'duration': 15},
    {'name': 'Steven', 'location': 'North Beach', 'start': time_to_minutes('13:30'), 'end': time_to_minutes('22:00'), 'duration': 45},
    {'name': 'Barbara', 'location': 'Fisherman\'s Wharf', 'start': time_to_minutes('18:00'), 'end': time_to_minutes('21:30'), 'duration': 30}
]

best_schedule = []
max_met = 0

for perm in itertools.permutations(friends):
    if perm[0]['name'] != 'John':
        continue
    current_location = 'Nob Hill'
    current_time = time_to_minutes('9:00')
    schedule = []
    met = 0
    possible = True
    
    for friend in perm:
        travel = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel
        start_time = max(arrival_time, friend['start'])
        
        if start_time + friend['duration'] > friend['end']:
            possible = False
            break
        
        schedule.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(start_time + friend['duration'])
        })
        
        current_time = start_time + friend['duration']
        current_location = friend['location']
        met += 1
    
    if possible and met > max_met or (possible and met == max_met and current_time < sum(time_to_minutes(entry["end_time"]) for entry in best_schedule[-1:])/max_met if best_schedule else 0):
        best_schedule = schedule
        max_met = met

print(json.dumps({"itinerary": best_schedule}, indent=2))