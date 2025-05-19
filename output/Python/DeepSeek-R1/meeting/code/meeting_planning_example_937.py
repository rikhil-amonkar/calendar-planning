import json

def parse_time(time_str):
    time_str = time_str.replace(' ', '').upper()
    hh_mm, period = time_str[:-2], time_str[-2:]
    hours, mins = map(int, hh_mm.split(':'))
    if period == 'PM' and hours != 12:
        hours += 12
    if period == 'AM' and hours == 12:
        hours = 0
    return hours * 60 + mins

travel_times = {
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Union Square'): 10,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Richmond District'): 14,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Presidio'): 14,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Presidio'): 16,
    ('Union Square', 'Russian Hill'): 13,
    ('Union Square', 'Sunset District'): 27,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Marina District'): 18,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'The Castro'): 17,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Presidio'): 24,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Sunset District'): 24,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Presidio'): 17,
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Embarcadero'): 14,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Presidio'): 10,
    ('Richmond District', 'Russian Hill'): 13,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Marina District'): 9,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'The Castro'): 16,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Presidio'): 7,
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Presidio'): 22,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Marina District'): 12,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'The Castro'): 25,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Presidio'): 20,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Union Square'): 19,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Richmond District'): 16,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Embarcadero'): 22,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Presidio'): 20,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Richmond District'): 11,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Presidio'): 17,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Nob Hill'): 18,
    ('Presidio', 'Marina District'): 11,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Alamo Square'): 19,
}

friends = [
    {'name': 'David', 'location': 'Sunset District', 'start': parse_time('9:15AM'), 'end': parse_time('10:00PM'), 'duration': 15},
    {'name': 'Kenneth', 'location': 'Union Square', 'start': parse_time('9:15PM'), 'end': parse_time('9:45PM'), 'duration': 15},
    {'name': 'Patricia', 'location': 'Nob Hill', 'start': parse_time('3:00PM'), 'end': parse_time('7:15PM'), 'duration': 120},
    {'name': 'Mary', 'location': 'Marina District', 'start': parse_time('2:45PM'), 'end': parse_time('4:45PM'), 'duration': 45},
    {'name': 'Charles', 'location': 'Richmond District', 'start': parse_time('5:15PM'), 'end': parse_time('9:00PM'), 'duration': 15},
    {'name': 'Joshua', 'location': 'Financial District', 'start': parse_time('2:30PM'), 'end': parse_time('5:15PM'), 'duration': 90},
    {'name': 'Ronald', 'location': 'Embarcadero', 'start': parse_time('6:15PM'), 'end': parse_time('8:45PM'), 'duration': 30},
    {'name': 'George', 'location': 'The Castro', 'start': parse_time('2:15PM'), 'end': parse_time('7:00PM'), 'duration': 105},
    {'name': 'Kimberly', 'location': 'Alamo Square', 'start': parse_time('9:00AM'), 'end': parse_time('2:30PM'), 'duration': 105},
    {'name': 'William', 'location': 'Presidio', 'start': parse_time('7:00AM'), 'end': parse_time('12:45PM'), 'duration': 60},
]

current_time = parse_time('9:00AM')
current_location = 'Russian Hill'
itinerary = []
remaining = friends.copy()

while True:
    best = None
    min_end = float('inf')
    for friend in remaining:
        from_loc = current_location
        to_loc = friend['location']
        tt = travel_times.get((from_loc, to_loc)) or travel_times.get((to_loc, from_loc), 0)
        arrive = current_time + tt
        start = max(arrive, friend['start'])
        end = start + friend['duration']
        if end > friend['end']:
            continue
        if end < min_end:
            min_end = end
            best = (friend, start, end)
    if not best:
        break
    f, s, e = best
    itinerary.append({
        'action': 'meet',
        'location': f['location'],
        'person': f['name'],
        'start_time': f"{s//60}:{s%60:02d}".replace(':00', '') if s%60 != 0 else f"{s//60}",
        'end_time': f"{e//60}:{e%60:02d}".replace(':00', '') if e%60 != 0 else f"{e//60}"
    })
    current_time = e
    current_location = f['location']
    remaining.remove(f)

print(json.dumps({'itinerary': itinerary}, indent=2))