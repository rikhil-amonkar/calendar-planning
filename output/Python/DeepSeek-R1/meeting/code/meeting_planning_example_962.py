import json

def time_to_min(time_str):
    time_str = time_str.replace(' ', '').upper()
    if 'AM' in time_str:
        time_part = time_str.replace('AM', '')
        h, m = time_part.split(':') if ':' in time_part else (time_part, '00')
        h = int(h)
        if h == 12:
            h = 0
        return h * 60 + int(m)
    else:
        time_part = time_str.replace('PM', '')
        h, m = time_part.split(':') if ':' in time_part else (time_part, '00')
        h = int(h)
        if h != 12:
            h += 12
        return h * 60 + int(m)

def min_to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours}:{minutes:02d}"

travel_pairs = [
    ('The Castro', 'Marina District', 21),
    ('The Castro', 'Presidio', 20),
    ('The Castro', 'North Beach', 20),
    ('The Castro', 'Embarcadero', 22),
    ('The Castro', 'Haight-Ashbury', 6),
    ('The Castro', 'Golden Gate Park', 11),
    ('The Castro', 'Richmond District', 16),
    ('The Castro', 'Alamo Square', 8),
    ('The Castro', 'Financial District', 21),
    ('The Castro', 'Sunset District', 17),
    ('Marina District', 'The Castro', 22),
    ('Marina District', 'Presidio', 10),
    ('Marina District', 'North Beach', 11),
    ('Marina District', 'Embarcadero', 14),
    ('Marina District', 'Haight-Ashbury', 16),
    ('Marina District', 'Golden Gate Park', 18),
    ('Marina District', 'Richmond District', 11),
    ('Marina District', 'Alamo Square', 15),
    ('Marina District', 'Financial District', 17),
    ('Marina District', 'Sunset District', 19),
    ('Presidio', 'The Castro', 21),
    ('Presidio', 'Marina District', 11),
    ('Presidio', 'North Beach', 18),
    ('Presidio', 'Embarcadero', 20),
    ('Presidio', 'Haight-Ashbury', 15),
    ('Presidio', 'Golden Gate Park', 12),
    ('Presidio', 'Richmond District', 7),
    ('Presidio', 'Alamo Square', 19),
    ('Presidio', 'Financial District', 23),
    ('Presidio', 'Sunset District', 15),
    ('North Beach', 'The Castro', 23),
    ('North Beach', 'Marina District', 9),
    ('North Beach', 'Presidio', 17),
    ('North Beach', 'Embarcadero', 6),
    ('North Beach', 'Haight-Ashbury', 18),
    ('North Beach', 'Golden Gate Park', 22),
    ('North Beach', 'Richmond District', 18),
    ('North Beach', 'Alamo Square', 16),
    ('North Beach', 'Financial District', 8),
    ('North Beach', 'Sunset District', 27),
    ('Embarcadero', 'The Castro', 25),
    ('Embarcadero', 'Marina District', 12),
    ('Embarcadero', 'Presidio', 20),
    ('Embarcadero', 'North Beach', 5),
    ('Embarcadero', 'Haight-Ashbury', 21),
    ('Embarcadero', 'Golden Gate Park', 25),
    ('Embarcadero', 'Richmond District', 21),
    ('Embarcadero', 'Alamo Square', 19),
    ('Embarcadero', 'Financial District', 5),
    ('Embarcadero', 'Sunset District', 30),
    ('Haight-Ashbury', 'The Castro', 6),
    ('Haight-Ashbury', 'Marina District', 17),
    ('Haight-Ashbury', 'Presidio', 15),
    ('Haight-Ashbury', 'North Beach', 19),
    ('Haight-Ashbury', 'Embarcadero', 20),
    ('Haight-Ashbury', 'Golden Gate Park', 7),
    ('Haight-Ashbury', 'Richmond District', 10),
    ('Haight-Ashbury', 'Alamo Square', 5),
    ('Haight-Ashbury', 'Financial District', 21),
    ('Haight-Ashbury', 'Sunset District', 15),
    ('Golden Gate Park', 'The Castro', 13),
    ('Golden Gate Park', 'Marina District', 16),
    ('Golden Gate Park', 'Presidio', 11),
    ('Golden Gate Park', 'North Beach', 23),
    ('Golden Gate Park', 'Embarcadero', 25),
    ('Golden Gate Park', 'Haight-Ashbury', 7),
    ('Golden Gate Park', 'Richmond District', 7),
    ('Golden Gate Park', 'Alamo Square', 9),
    ('Golden Gate Park', 'Financial District', 26),
    ('Golden Gate Park', 'Sunset District', 10),
    ('Richmond District', 'The Castro', 16),
    ('Richmond District', 'Marina District', 9),
    ('Richmond District', 'Presidio', 7),
    ('Richmond District', 'North Beach', 17),
    ('Richmond District', 'Embarcadero', 19),
    ('Richmond District', 'Haight-Ashbury', 10),
    ('Richmond District', 'Golden Gate Park', 9),
    ('Richmond District', 'Alamo Square', 13),
    ('Richmond District', 'Financial District', 22),
    ('Richmond District', 'Sunset District', 11),
    ('Alamo Square', 'The Castro', 8),
    ('Alamo Square', 'Marina District', 15),
    ('Alamo Square', 'Presidio', 17),
    ('Alamo Square', 'North Beach', 15),
    ('Alamo Square', 'Embarcadero', 16),
    ('Alamo Square', 'Haight-Ashbury', 5),
    ('Alamo Square', 'Golden Gate Park', 9),
    ('Alamo Square', 'Richmond District', 11),
    ('Alamo Square', 'Financial District', 17),
    ('Alamo Square', 'Sunset District', 16),
    ('Financial District', 'The Castro', 20),
    ('Financial District', 'Marina District', 15),
    ('Financial District', 'Presidio', 22),
    ('Financial District', 'North Beach', 7),
    ('Financial District', 'Embarcadero', 4),
    ('Financial District', 'Haight-Ashbury', 19),
    ('Financial District', 'Golden Gate Park', 23),
    ('Financial District', 'Richmond District', 21),
    ('Financial District', 'Alamo Square', 17),
    ('Financial District', 'Sunset District', 30),
    ('Sunset District', 'The Castro', 17),
    ('Sunset District', 'Marina District', 21),
    ('Sunset District', 'Presidio', 16),
    ('Sunset District', 'North Beach', 28),
    ('Sunset District', 'Embarcadero', 30),
    ('Sunset District', 'Haight-Ashbury', 15),
    ('Sunset District', 'Golden Gate Park', 11),
    ('Sunset District', 'Richmond District', 12),
    ('Sunset District', 'Alamo Square', 17),
    ('Sunset District', 'Financial District', 30),
]

travel_times = {}
for pair in travel_pairs:
    from_loc, to_loc, time = pair
    travel_times[(from_loc, to_loc)] = time

friends = [
    {'name': 'Elizabeth', 'location': 'Marina District', 'start': time_to_min('7:00PM'), 'end': time_to_min('8:45PM'), 'duration': 105},
    {'name': 'Joshua', 'location': 'Presidio', 'start': time_to_min('8:30AM'), 'end': time_to_min('1:15PM'), 'duration': 105},
    {'name': 'Timothy', 'location': 'North Beach', 'start': time_to_min('7:45PM'), 'end': time_to_min('10:00PM'), 'duration': 90},
    {'name': 'David', 'location': 'Embarcadero', 'start': time_to_min('10:45AM'), 'end': time_to_min('12:30PM'), 'duration': 30},
    {'name': 'Kimberly', 'location': 'Haight-Ashbury', 'start': time_to_min('4:45PM'), 'end': time_to_min('9:30PM'), 'duration': 75},
    {'name': 'Lisa', 'location': 'Golden Gate Park', 'start': time_to_min('5:30PM'), 'end': time_to_min('9:45PM'), 'duration': 45},
    {'name': 'Stephanie', 'location': 'Alamo Square', 'start': time_to_min('3:30PM'), 'end': time_to_min('4:30PM'), 'duration': 30},
    {'name': 'Helen', 'location': 'Financial District', 'start': time_to_min('5:30PM'), 'end': time_to_min('6:30PM'), 'duration': 45},
    {'name': 'Laura', 'location': 'Sunset District', 'start': time_to_min('5:45PM'), 'end': time_to_min('9:15PM'), 'duration': 90},
]

current_time = time_to_min('9:00AM')
current_location = 'The Castro'
itinerary = []
remaining_friends = friends.copy()

while True:
    possible = []
    for friend in remaining_friends:
        to_loc = friend['location']
        key = (current_location, to_loc)
        if key not in travel_times:
            continue
        travel_time = travel_times[key]
        arrival = current_time + travel_time
        start = max(arrival, friend['start'])
        if start + friend['duration'] > friend['end']:
            continue
        possible.append( (start + friend['duration'], friend, start) )
    if not possible:
        break
    possible.sort()
    best_end, best_friend, best_start = possible[0]
    itinerary.append({
        'action': 'meet',
        'location': best_friend['location'],
        'person': best_friend['name'],
        'start_time': min_to_time(best_start),
        'end_time': min_to_time(best_end)
    })
    current_time = best_end
    current_location = best_friend['location']
    remaining_friends.remove(best_friend)

print(json.dumps({'itinerary': itinerary}, indent=2))