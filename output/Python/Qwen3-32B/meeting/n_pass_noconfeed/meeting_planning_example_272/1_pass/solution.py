import itertools
import json

def time_to_minutes(t_str):
    h, m = map(int, t_str.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

travel_times = {
    'Russian Hill': {'Nob Hill': 5, 'Mission District': 16, 'Embarcadero': 8},
    'Nob Hill': {'Russian Hill': 5, 'Mission District': 13, 'Embarcadero': 9},
    'Mission District': {'Russian Hill': 15, 'Nob Hill': 12, 'Embarcadero': 19},
    'Embarcadero': {'Russian Hill': 8, 'Nob Hill': 10, 'Mission District': 20},
}

friends = [
    {
        'name': 'Timothy',
        'location': 'Embarcadero',
        'available_start': time_to_minutes('9:45'),
        'available_end': time_to_minutes('17:45'),
        'required_duration': 120
    },
    {
        'name': 'Patricia',
        'location': 'Nob Hill',
        'available_start': time_to_minutes('18:30'),
        'available_end': time_to_minutes('21:45'),
        'required_duration': 90
    },
    {
        'name': 'Ashley',
        'location': 'Mission District',
        'available_start': time_to_minutes('20:30'),
        'available_end': time_to_minutes('21:15'),
        'required_duration': 45
    }
]

best_itinerary = []
max_meetings = 0

for perm in itertools.permutations(friends):
    current_time = time_to_minutes('9:00')  # 540
    current_location = 'Russian Hill'
    itinerary = []
    valid = True
    for friend in perm:
        dest = friend['location']
        travel_time = travel_times[current_location][dest]
        current_time += travel_time
        
        earliest_start = max(current_time, friend['available_start'])
        if earliest_start + friend['required_duration'] > friend['available_end']:
            valid = False
            break
            
        meeting_start = earliest_start
        meeting_end = earliest_start + friend['required_duration']
        
        itinerary.append({
            'action': 'meet',
            'location': dest,
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = dest
    
    if valid and len(itinerary) > max_meetings:
        max_meetings = len(itinerary)
        best_itinerary = itinerary

result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))