import json
from itertools import permutations

def time_to_minutes(t):
    hours, mins = map(int, t.split(':'))
    return hours * 60 + mins

def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours}:{mins:02d}".lstrip('0') if hours != 0 else f"{hours}:{mins:02d}"

friends = [
    {
        'name': 'Barbara',
        'location': 'Golden Gate Park',
        'available_start': time_to_minutes('8:15'),
        'available_end': time_to_minutes('19:00'),
        'duration': 45,
    },
    {
        'name': 'Kenneth',
        'location': 'Chinatown',
        'available_start': time_to_minutes('12:00'),
        'available_end': time_to_minutes('15:00'),
        'duration': 90,
    }
]

travel_times = {
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Chinatown'): 5,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Chinatown'): 23,
}

start_location = 'Financial District'
start_time = time_to_minutes('9:00')

best = {"friends": 0, "end": float('inf'), "schedule": []}

for perm in permutations(friends):
    current_loc = start_location
    current_time = start_time
    schedule = []
    valid = True
    
    for i, f in enumerate(perm):
        travel_key = (current_loc, f['location'])
        if travel_key not in travel_times:
            valid = False
            break
        arrival = current_time + travel_times[travel_key]
        start = max(arrival, f['available_start'])
        
        if i < len(perm)-1:
            next_travel = travel_times[(f['location'], perm[i+1]['location'])]
            desired_end = perm[i+1]['available_start'] - next_travel
            desired_start = desired_end - f['duration']
            start = max(start, desired_start)
        
        end = start + f['duration']
        if end > f['available_end']:
            valid = False
            break
        
        schedule.append({
            "action": "meet",
            "location": f['location'],
            "person": f['name'],
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
        current_time = end
        current_loc = f['location']
    
    if valid:
        met = len(perm)
        if met > best["friends"] or (met == best["friends"] and current_time < best["end"]):
            best = {"friends": met, "end": current_time, "schedule": schedule}

print(json.dumps({"itinerary": best["schedule"]}, indent=2))