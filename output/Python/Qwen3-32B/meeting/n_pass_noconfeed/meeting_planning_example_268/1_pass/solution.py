import itertools
import json

def time_str_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

travel_times = {
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Presidio'): 18,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Alamo Square'): 18,
    ('Presidio', 'Russian Hill'): 14,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Presidio'): 14,
}

friends = [
    {
        'name': 'Timothy',
        'location': 'Alamo Square',
        'available_start': time_str_to_minutes('12:00'),
        'available_end': time_str_to_minutes('16:15'),
        'required_duration': 105
    },
    {
        'name': 'Mark',
        'location': 'Presidio',
        'available_start': time_str_to_minutes('18:45'),
        'available_end': time_str_to_minutes('21:00'),
        'required_duration': 60
    },
    {
        'name': 'Joseph',
        'location': 'Russian Hill',
        'available_start': time_str_to_minutes('16:45'),
        'available_end': time_str_to_minutes('21:30'),
        'required_duration': 60
    }
]

best_itinerary = []
best_length = 0

for r in [3, 2, 1]:
    for perm in itertools.permutations(friends, r):
        current_time = time_str_to_minutes('9:00')
        current_location = 'Golden Gate Park'
        itinerary = []
        valid = True
        for friend in perm:
            travel_time = travel_times.get((current_location, friend['location']))
            if travel_time is None:
                valid = False
                break
            current_time += travel_time
            meeting_start = max(current_time, friend['available_start'])
            if meeting_start + friend['required_duration'] > friend['available_end']:
                valid = False
                break
            meeting_end = meeting_start + friend['required_duration']
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time_str(meeting_start),
                'end_time': minutes_to_time_str(meeting_end)
            })
            current_time = meeting_end
            current_location = friend['location']
        if valid:
            if len(itinerary) > best_length:
                best_length = len(itinerary)
                best_itinerary = itinerary
    if best_length == 3:
        break

result = {
    "itinerary": best_itinerary
}
print(json.dumps(result, indent=2))