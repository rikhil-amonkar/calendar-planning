import json
from itertools import permutations

def to_minutes(time_str):
    hours, mins = map(int, time_str.split(':'))
    return hours * 60 + mins

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

friends = [
    {
        'name': 'Timothy',
        'location': 'Alamo Square',
        'available_start': to_minutes('12:00'),
        'available_end': to_minutes('16:15'),
        'min_duration': 105,
    },
    {
        'name': 'Joseph',
        'location': 'Russian Hill',
        'available_start': to_minutes('16:45'),
        'available_end': to_minutes('21:30'),
        'min_duration': 60,
    },
    {
        'name': 'Mark',
        'location': 'Presidio',
        'available_start': to_minutes('18:45'),
        'available_end': to_minutes('21:00'),
        'min_duration': 60,
    },
]

travel_times = {
    'Golden Gate Park': {'Alamo Square': 10, 'Presidio': 11, 'Russian Hill': 19},
    'Alamo Square': {'Golden Gate Park': 9, 'Presidio': 18, 'Russian Hill': 13},
    'Presidio': {'Golden Gate Park': 12, 'Alamo Square': 18, 'Russian Hill': 14},
    'Russian Hill': {'Golden Gate Park': 21, 'Alamo Square': 15, 'Presidio': 14},
}

def simulate_schedule(perm, start_time, start_loc, travel):
    current_time = start_time
    current_loc = start_loc
    itinerary = []
    total_wait = 0
    for f in perm:
        travel_time = travel[current_loc].get(f['location'], 0)
        arrival = current_time + travel_time
        avail_start = f['available_start']
        avail_end = f['available_end']
        duration = f['min_duration']
        start = max(arrival, avail_start)
        if start + duration > avail_end:
            return None, None
        wait = max(0, avail_start - arrival)
        total_wait += wait
        itinerary.append({
            'loc': f['location'],
            'person': f['name'],
            'start': start,
            'end': start + duration
        })
        current_time = start + duration
        current_loc = f['location']
    return itinerary, total_wait

start_min = to_minutes('9:00')
start_loc = 'Golden Gate Park'
timothy = next(f for f in friends if f['name'] == 'Timothy')
others = [f for f in friends if f['name'] != 'Timothy']
valid_perms = []

for p in permutations(others):
    valid_perms.append([timothy] + list(p))

best = None
max_met = 0
min_wait = float('inf')

for perm in valid_perms:
    itinerary, wait = simulate_schedule(perm, start_min, start_loc, travel_times)
    if itinerary:
        met = len(itinerary)
        if met > max_met or (met == max_met and wait < min_wait):
            max_met = met
            min_wait = wait
            best = itinerary

output = {"itinerary": []}
if best:
    for entry in best:
        output["itinerary"].append({
            "action": "meet",
            "location": entry['loc'],
            "person": entry['person'],
            "start_time": to_time_str(entry['start']),
            "end_time": to_time_str(entry['end'])
        })

print(json.dumps(output))