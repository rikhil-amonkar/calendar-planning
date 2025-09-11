import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

travel_times = {
    ('North Beach', 'Mission District'): 18,
    ('North Beach', 'The Castro'): 22,
    ('Mission District', 'North Beach'): 17,
    ('Mission District', 'The Castro'): 7,
    ('The Castro', 'North Beach'): 20,
    ('The Castro', 'Mission District'): 7,
}

friends = [
    {
        'name': 'James',
        'location': 'Mission District',
        'available_start': time_to_minutes('12:45'),
        'available_end': time_to_minutes('14:00'),
        'required_duration': 75
    },
    {
        'name': 'Robert',
        'location': 'The Castro',
        'available_start': time_to_minutes('12:45'),
        'available_end': time_to_minutes('15:15'),
        'required_duration': 30
    }
]

initial_time = time_to_minutes('9:00')  # 540
initial_location = 'North Beach'

best_itinerary = []
max_friends = 0

for order in permutations(friends):
    current_time = initial_time
    current_location = initial_location
    itinerary = []
    friends_met = 0
    
    for friend in order:
        travel_time = travel_times.get((current_location, friend['location']))
        current_time += travel_time
        current_location = friend['location']
        
        earliest_start = max(current_time, friend['available_start'])
        meeting_end = earliest_start + friend['required_duration']
        
        if meeting_end <= friend['available_end']:
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(earliest_start),
                'end_time': minutes_to_time(meeting_end)
            })
            friends_met += 1
            current_time = meeting_end
        else:
            break
    
    if friends_met > max_friends:
        max_friends = friends_met
        best_itinerary = itinerary

result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))