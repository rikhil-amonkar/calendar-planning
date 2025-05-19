import itertools
import json

def time_to_minutes(time_str):
    hours, mins = map(int, time_str.split(':'))
    return hours * 60 + mins

def minutes_to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours}:{minutes:02d}"

friends = [
    {
        'name': 'Melissa',
        'location': 'North Beach',
        'available_start': time_to_minutes('8:15'),
        'available_end': time_to_minutes('13:30'),
        'min_duration': 105
    },
    {
        'name': 'Anthony',
        'location': 'Chinatown',
        'available_start': time_to_minutes('13:15'),
        'available_end': time_to_minutes('14:30'),
        'min_duration': 60
    },
    {
        'name': 'Rebecca',
        'location': 'Russian Hill',
        'available_start': time_to_minutes('19:30'),
        'available_end': time_to_minutes('21:15'),
        'min_duration': 105
    }
]

travel_times = {
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'North Beach'): 29,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'North Beach'): 3,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'North Beach'): 5,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Russian Hill'): 4,
}

best_itinerary = []
max_met = 0
best_end = float('inf')

for perm in itertools.permutations(friends):
    current_loc = 'Sunset District'
    current_time = 540
    itinerary = []
    
    for friend in perm:
        travel_key = (current_loc, friend['location'])
        if travel_key not in travel_times:
            continue
        travel = travel_times[travel_key]
        arrive = current_time + travel
        start = max(arrive, friend['available_start'])
        end = start + friend['min_duration']
        
        if end <= friend['available_end']:
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(start).replace('0','', 1) if minutes_to_time(start).startswith('0') else minutes_to_time(start),
                'end_time': minutes_to_time(end).replace('0','', 1) if minutes_to_time(end).startswith('0') else minutes_to_time(end)
            })
            current_loc = friend['location']
            current_time = end
    
    if len(itinerary) > max_met or (len(itinerary) == max_met and current_time < best_end):
        max_met = len(itinerary)
        best_itinerary = itinerary.copy()
        best_end = current_time

print(json.dumps({'itinerary': best_itinerary}))