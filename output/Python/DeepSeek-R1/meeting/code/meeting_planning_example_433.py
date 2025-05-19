import itertools
import json

def time_to_minutes(t_str):
    h, m = map(int, t_str.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}" if mm != 0 else f"{h}:00"

friends = [
    {
        'name': 'Emily',
        'location': 'Richmond District',
        'available_start': time_to_minutes('19:00'),
        'available_end': time_to_minutes('21:00'),
        'duration': 15
    },
    {
        'name': 'Margaret',
        'location': 'Financial District',
        'available_start': time_to_minutes('16:30'),
        'available_end': time_to_minutes('20:15'),
        'duration': 75
    },
    {
        'name': 'Ronald',
        'location': 'North Beach',
        'available_start': time_to_minutes('18:30'),
        'available_end': time_to_minutes('19:30'),
        'duration': 45
    },
    {
        'name': 'Deborah',
        'location': 'The Castro',
        'available_start': time_to_minutes('13:45'),
        'available_end': time_to_minutes('21:15'),
        'duration': 90
    },
    {
        'name': 'Jeffrey',
        'location': 'Golden Gate Park',
        'available_start': time_to_minutes('11:15'),
        'available_end': time_to_minutes('14:30'),
        'duration': 120
    }
]

travel_times = {
    ('Nob Hill', 'Richmond District'):14,
    ('Nob Hill', 'Financial District'):9,
    ('Nob Hill', 'North Beach'):8,
    ('Nob Hill', 'The Castro'):17,
    ('Nob Hill', 'Golden Gate Park'):17,
    ('Richmond District', 'Nob Hill'):17,
    ('Richmond District', 'Financial District'):22,
    ('Richmond District', 'North Beach'):17,
    ('Richmond District', 'The Castro'):16,
    ('Richmond District', 'Golden Gate Park'):9,
    ('Financial District', 'Nob Hill'):8,
    ('Financial District', 'Richmond District'):21,
    ('Financial District', 'North Beach'):7,
    ('Financial District', 'The Castro'):23,
    ('Financial District', 'Golden Gate Park'):23,
    ('North Beach', 'Nob Hill'):7,
    ('North Beach', 'Richmond District'):18,
    ('North Beach', 'Financial District'):8,
    ('North Beach', 'The Castro'):22,
    ('North Beach', 'Golden Gate Park'):22,
    ('The Castro', 'Nob Hill'):16,
    ('The Castro', 'Richmond District'):16,
    ('The Castro', 'Financial District'):20,
    ('The Castro', 'North Beach'):20,
    ('The Castro', 'Golden Gate Park'):11,
    ('Golden Gate Park', 'Nob Hill'):20,
    ('Golden Gate Park', 'Richmond District'):7,
    ('Golden Gate Park', 'Financial District'):26,
    ('Golden Gate Park', 'North Beach'):24,
    ('Golden Gate Park', 'The Castro'):13,
}

best_itinerary = None
max_count = 0
min_end_time = float('inf')

for r in range(len(friends), 0, -1):
    for perm in itertools.permutations(friends, r):
        current_loc = 'Nob Hill'
        current_time = 540  # 9:00 AM
        itinerary = []
        valid = True
        
        for friend in perm:
            from_to = (current_loc, friend['location'])
            tt = travel_times.get(from_to)
            if tt is None:
                valid = False
                break
            arrival = current_time + tt
            start = max(arrival, friend['available_start'])
            end = start + friend['duration']
            if end > friend['available_end']:
                valid = False
                break
            itinerary.append({
                "action": "meet",
                "location": friend['location'],
                "person": friend['name'],
                "start_time": minutes_to_time(start).lstrip('0'),
                "end_time": minutes_to_time(end).lstrip('0')
            })
            current_time = end
            current_loc = friend['location']
        
        if valid:
            if r > max_count or (r == max_count and current_time < min_end_time):
                max_count = r
                best_itinerary = itinerary
                min_end_time = current_time
    if best_itinerary and max_count == len(friends):
        break

print(json.dumps({"itinerary": best_itinerary} if best_itinerary else {"itinerary": []}))