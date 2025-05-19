import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input data
travel_times = {
    'Mission District': {
        'The Castro': 7,
        'Nob Hill': 12,
        'Presidio': 25,
        'Marina District': 19,
        'Pacific Heights': 16,
        'Golden Gate Park': 17,
        'Chinatown': 16,
        'Richmond District': 20
    },
    'The Castro': {
        'Mission District': 7,
        'Nob Hill': 16,
        'Presidio': 20,
        'Marina District': 21,
        'Pacific Heights': 16,
        'Golden Gate Park': 11,
        'Chinatown': 22,
        'Richmond District': 16
    },
    'Nob Hill': {
        'Mission District': 13,
        'The Castro': 17,
        'Presidio': 17,
        'Marina District': 11,
        'Pacific Heights': 8,
        'Golden Gate Park': 17,
        'Chinatown': 6,
        'Richmond District': 14
    },
    'Presidio': {
        'Mission District': 26,
        'The Castro': 21,
        'Nob Hill': 18,
        'Marina District': 11,
        'Pacific Heights': 11,
        'Golden Gate Park': 12,
        'Chinatown': 21,
        'Richmond District': 7
    },
    'Marina District': {
        'Mission District': 20,
        'The Castro': 22,
        'Nob Hill': 12,
        'Presidio': 10,
        'Pacific Heights': 7,
        'Golden Gate Park': 18,
        'Chinatown': 15,
        'Richmond District': 11
    },
    'Pacific Heights': {
        'Mission District': 15,
        'The Castro': 16,
        'Nob Hill': 8,
        'Presidio': 11,
        'Marina District': 6,
        'Golden Gate Park': 15,
        'Chinatown': 11,
        'Richmond District': 12
    },
    'Golden Gate Park': {
        'Mission District': 17,
        'The Castro': 13,
        'Nob Hill': 20,
        'Presidio': 11,
        'Marina District': 16,
        'Pacific Heights': 16,
        'Chinatown': 23,
        'Richmond District': 7
    },
    'Chinatown': {
        'Mission District': 17,
        'The Castro': 22,
        'Nob Hill': 9,
        'Presidio': 19,
        'Marina District': 12,
        'Pacific Heights': 10,
        'Golden Gate Park': 23,
        'Richmond District': 20
    },
    'Richmond District': {
        'Mission District': 20,
        'The Castro': 16,
        'Nob Hill': 17,
        'Presidio': 7,
        'Marina District': 9,
        'Pacific Heights': 10,
        'Golden Gate Park': 9,
        'Chinatown': 20
    }
}

friends = [
    {
        'name': 'Lisa',
        'location': 'The Castro',
        'available_start': '19:15',
        'available_end': '21:15',
        'min_duration': 120
    },
    {
        'name': 'Daniel',
        'location': 'Nob Hill',
        'available_start': '8:15',
        'available_end': '11:00',
        'min_duration': 15
    },
    {
        'name': 'Elizabeth',
        'location': 'Presidio',
        'available_start': '21:15',
        'available_end': '22:15',
        'min_duration': 45
    },
    {
        'name': 'Steven',
        'location': 'Marina District',
        'available_start': '16:30',
        'available_end': '20:45',
        'min_duration': 90
    },
    {
        'name': 'Timothy',
        'location': 'Pacific Heights',
        'available_start': '12:00',
        'available_end': '18:00',
        'min_duration': 90
    },
    {
        'name': 'Ashley',
        'location': 'Golden Gate Park',
        'available_start': '20:45',
        'available_end': '21:45',
        'min_duration': 60
    },
    {
        'name': 'Kevin',
        'location': 'Chinatown',
        'available_start': '12:00',
        'available_end': '19:00',
        'min_duration': 30
    },
    {
        'name': 'Betty',
        'location': 'Richmond District',
        'available_start': '13:15',
        'available_end': '15:45',
        'min_duration': 30
    }
]

current_location = 'Mission District'
current_time = time_to_minutes('9:00')

def evaluate_schedule(order):
    global current_location, current_time
    itinerary = []
    temp_location = current_location
    temp_time = current_time
    
    for friend_idx in order:
        friend = friends[friend_idx]
        location = friend['location']
        travel_time = travel_times[temp_location][location]
        
        arrival_time = temp_time + travel_time
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        min_duration = friend['min_duration']
        
        start_time = max(arrival_time, available_start)
        end_time = min(start_time + min_duration, available_end)
        
        if end_time - start_time < min_duration:
            return None
        
        itinerary.append({
            'action': 'meet',
            'location': location,
            'person': friend['name'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        
        temp_location = location
        temp_time = end_time
    
    return itinerary

best_itinerary = None
max_meetings = 0

# Try all possible orders of meeting friends
for order in permutations(range(len(friends))):
    itinerary = evaluate_schedule(order)
    if itinerary and len(itinerary) > max_meetings:
        max_meetings = len(itinerary)
        best_itinerary = itinerary
    elif itinerary and len(itinerary) == max_meetings:
        # Prefer longer total meeting time
        current_duration = sum(time_to_minutes(item['end_time']) - time_to_minutes(item['start_time']) for item in itinerary)
        best_duration = sum(time_to_minutes(item['end_time']) - time_to_minutes(item['start_time']) for item in best_itinerary)
        if current_duration > best_duration:
            best_itinerary = itinerary

# After finding the best itinerary, check if we can add more meetings
if best_itinerary:
    remaining_friends = [f for f in friends if f['name'] not in [item['person'] for item in best_itinerary]]
    
    for friend in remaining_friends:
        last_meeting = best_itinerary[-1]
        temp_location = last_meeting['location']
        temp_time = time_to_minutes(last_meeting['end_time'])
        
        location = friend['location']
        travel_time = travel_times[temp_location][location]
        
        arrival_time = temp_time + travel_time
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        min_duration = friend['min_duration']
        
        start_time = max(arrival_time, available_start)
        end_time = min(start_time + min_duration, available_end)
        
        if end_time - start_time >= min_duration:
            best_itinerary.append({
                'action': 'meet',
                'location': location,
                'person': friend['name'],
                'start_time': minutes_to_time(start_time),
                'end_time': minutes_to_time(end_time)
            })

output = {"itinerary": best_itinerary} if best_itinerary else {"itinerary": []}
print(json.dumps(output, indent=2))