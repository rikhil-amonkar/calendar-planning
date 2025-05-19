import itertools
import json

travel_times = {
    ('North Beach', 'Pacific Heights'): 8,
    ('North Beach', 'Embarcadero'): 6,
    ('Pacific Heights', 'North Beach'): 9,
    ('Pacific Heights', 'Embarcadero'): 10,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Pacific Heights'): 11,
}

friends = [
    {
        'name': 'Karen',
        'location': 'Pacific Heights',
        'start': 1125,  # 18:45 (6:45 PM)
        'end': 1230,    # 20:30 (8:30 PM)
        'duration': 90
    },
    {
        'name': 'Mark',
        'location': 'Embarcadero',
        'start': 780,   # 13:00 (1:00 PM)
        'end': 1085,   # 17:45 (5:45 PM)
        'duration': 120
    }
]

def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours}:{mins:02d}"

best_itinerary = []
max_meetings = 0

for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM
    current_location = 'North Beach'
    itinerary = []
    
    for friend in perm:
        travel = travel_times.get((current_location, friend['location']), None)
        if travel is None:
            continue
        
        arrival = current_time + travel
        meeting_start = max(arrival, friend['start'])
        meeting_end = meeting_start + friend['duration']
        
        if meeting_end > friend['end']:
            continue
        
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = friend['location']
    
    if len(itinerary) > max_meetings:
        max_meetings = len(itinerary)
        best_itinerary = itinerary

output = {
    "itinerary": best_itinerary
}

print(json.dumps(output))