import itertools
import json

def time_to_minutes(timestr):
    period = timestr[-2:]
    time_part = timestr[:-2].strip() if period in ['AM', 'PM'] else timestr
    hours, mins = map(int, time_part.split(':'))
    if period == 'PM' and hours != 12:
        hours += 12
    elif period == 'AM' and hours == 12:
        hours = 0
    return hours * 60 + mins

friends = [
    {'name': 'Rebecca', 'location': 'Fisherman\'s Wharf', 'start': time_to_minutes('8:00AM'), 'end': time_to_minutes('11:15AM'), 'duration': 30},
    {'name': 'Stephanie', 'location': 'Golden Gate Park', 'start': time_to_minutes('11:00AM'), 'end': time_to_minutes('3:00PM'), 'duration': 105},
    {'name': 'Karen', 'location': 'Chinatown', 'start': time_to_minutes('1:45PM'), 'end': time_to_minutes('4:30PM'), 'duration': 15},
    {'name': 'Brian', 'location': 'Union Square', 'start': time_to_minutes('3:00PM'), 'end': time_to_minutes('5:15PM'), 'duration': 30},
    {'name': 'Steven', 'location': 'North Beach', 'start': time_to_minutes('2:30PM'), 'end': time_to_minutes('8:45PM'), 'duration': 120}
]

travel_times = {
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'North Beach'): 7,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'North Beach'): 24,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'North Beach'): 3,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Fisherman\'s Wharf'): 15,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'North Beach'): 10,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Union Square'): 13,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Union Square'): 7,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Pacific Heights'): 8
}

best_itinerary = []
best_count = 0

for perm in itertools.permutations(friends):
    current_loc = 'Financial District'
    current_time = 540
    itinerary = []
    valid = True
    
    for friend in perm:
        travel_key = (current_loc, friend['location'])
        if travel_key not in travel_times:
            valid = False
            break
        travel = travel_times[travel_key]
        arrive = current_time + travel
        start = max(arrive, friend['start'])
        if start + friend['duration'] > friend['end']:
            valid = False
            break
        itinerary.append({
            'location': friend['location'],
            'person': friend['name'],
            'start_time': start,
            'end_time': start + friend['duration']
        })
        current_loc = friend['location']
        current_time = start + friend['duration']
    
    if valid:
        if len(itinerary) > best_count:
            best_count = len(itinerary)
            best_itinerary = itinerary.copy()
        elif len(itinerary) == best_count and best_itinerary:
            current_total = sum(e['end_time'] - e['start_time'] for e in itinerary)
            best_total = sum(e['end_time'] - e['start_time'] for e in best_itinerary)
            if current_total > best_total:
                best_itinerary = itinerary.copy()

def format_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}".replace(":00", ":0").replace(":0", ":") if m == 0 else f"{h}:{m:02d}"

formatted = []
for entry in best_itinerary:
    formatted.append({
        'action': 'meet',
        'location': entry['location'],
        'person': entry['person'],
        'start_time': format_time(entry['start_time']),
        'end_time': format_time(entry['end_time'])
    })

print(json.dumps({'itinerary': formatted}, indent=2))