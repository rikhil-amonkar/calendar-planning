import itertools
import json

def time_to_min(t_str):
    h, m = map(int, t_str.split(':'))
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h}:{m:02d}"

friends_data = [
    {
        'name': 'David',
        'location': 'Fisherman\'s Wharf',
        'start': time_to_min('10:45'),
        'end': time_to_min('15:30'),
        'duration': 15
    },
    {
        'name': 'Timothy',
        'location': 'Pacific Heights',
        'start': time_to_min('9:00'),
        'end': time_to_min('15:30'),
        'duration': 75
    },
    {
        'name': 'Robert',
        'location': 'Mission District',
        'start': time_to_min('12:15'),
        'end': time_to_min('19:45'),
        'duration': 90
    }
]

travel_times = {
    'Financial District': {
        'Fisherman\'s Wharf': 10,
        'Pacific Heights': 13,
        'Mission District': 17
    },
    'Fisherman\'s Wharf': {
        'Financial District': 11,
        'Pacific Heights': 12,
        'Mission District': 22
    },
    'Pacific Heights': {
        'Financial District': 13,
        'Fisherman\'s Wharf': 13,
        'Mission District': 15
    },
    'Mission District': {
        'Financial District': 17,
        'Fisherman\'s Wharf': 22,
        'Pacific Heights': 16
    }
}

best_schedule = None
max_friends = 0
min_end_time = float('inf')

for perm in itertools.permutations(friends_data):
    current_location = 'Financial District'
    current_time = time_to_min('9:00')
    temp_itinerary = []
    valid = True
    
    for friend in perm:
        to_loc = friend['location']
        travel_time = travel_times[current_location].get(to_loc, 0)
        arrival_time = current_time + travel_time
        
        if arrival_time > friend['end']:
            valid = False
            break
        
        meeting_start = max(arrival_time, friend['start'])
        meeting_end = meeting_start + friend['duration']
        
        if meeting_end > friend['end']:
            valid = False
            break
        
        temp_itinerary.append({
            'action': 'meet',
            'location': to_loc,
            'person': friend['name'],
            'start_time': min_to_time(meeting_start),
            'end_time': min_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = to_loc
    
    if valid:
        num_met = len(perm)
        if num_met > max_friends or (num_met == max_friends and current_time < min_end_time):
            max_friends = num_met
            min_end_time = current_time
            best_schedule = temp_itinerary.copy()

output = {"itinerary": best_schedule} if best_schedule else {"itinerary": []}
print(json.dumps(output, indent=2))