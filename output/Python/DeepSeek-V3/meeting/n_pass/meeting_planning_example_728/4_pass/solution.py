import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input data remains the same
travel_times = {
    'Marina District': {
        'Mission District': 20,
        'Fisherman\'s Wharf': 10,
        'Presidio': 10,
        'Union Square': 16,
        'Sunset District': 19,
        'Financial District': 17,
        'Haight-Ashbury': 16,
        'Russian Hill': 8
    },
    # ... (rest of travel_times remains unchanged)
}

friends = [
    {'name': 'Karen', 'location': 'Mission District', 'start': '14:15', 'end': '22:00', 'duration': 30},
    {'name': 'Richard', 'location': 'Fisherman\'s Wharf', 'start': '14:30', 'end': '17:30', 'duration': 30},
    {'name': 'Robert', 'location': 'Presidio', 'start': '21:45', 'end': '22:45', 'duration': 60},
    {'name': 'Joseph', 'location': 'Union Square', 'start': '11:45', 'end': '14:45', 'duration': 120},
    {'name': 'Helen', 'location': 'Sunset District', 'start': '14:45', 'end': '20:45', 'duration': 105},
    {'name': 'Elizabeth', 'location': 'Financial District', 'start': '10:00', 'end': '12:45', 'duration': 75},
    {'name': 'Kimberly', 'location': 'Haight-Ashbury', 'start': '14:15', 'end': '17:30', 'duration': 105},
    {'name': 'Ashley', 'location': 'Russian Hill', 'start': '11:30', 'end': '21:30', 'duration': 45}
]

def generate_best_itinerary():
    best_itinerary = []
    max_meetings = 0
    
    # Sort friends by their end times (earlier first)
    sorted_friends = sorted(friends, key=lambda x: time_to_minutes(x['end']))
    
    current_location = 'Marina District'
    current_time = time_to_minutes('9:00')
    itinerary = []
    
    for friend in sorted_friends:
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, time_to_minutes(friend['start']))
        meeting_end = meeting_start + friend['duration']
        
        if meeting_end <= time_to_minutes(friend['end']):
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            current_location = friend['location']
            current_time = meeting_end
    
    # Try another strategy - prioritize friends with tighter time windows
    if len(itinerary) < len(friends):
        # Sort by available window (end - start - duration)
        sorted_friends = sorted(friends, key=lambda x: (
            time_to_minutes(x['end']) - time_to_minutes(x['start']) - x['duration']
        ))
        
        current_location = 'Marina District'
        current_time = time_to_minutes('9:00')
        new_itinerary = []
        
        for friend in sorted_friends:
            travel_time = travel_times[current_location][friend['location']]
            arrival_time = current_time + travel_time
            meeting_start = max(arrival_time, time_to_minutes(friend['start']))
            meeting_end = meeting_start + friend['duration']
            
            if meeting_end <= time_to_minutes(friend['end']):
                new_itinerary.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                current_location = friend['location']
                current_time = meeting_end
        
        if len(new_itinerary) > len(itinerary):
            itinerary = new_itinerary
    
    return itinerary

itinerary = generate_best_itinerary()
print(json.dumps({"itinerary": itinerary}, indent=2))