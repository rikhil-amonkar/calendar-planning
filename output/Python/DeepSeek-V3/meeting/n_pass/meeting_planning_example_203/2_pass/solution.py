import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times in minutes between locations
travel_times = {
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Mission District'): 17,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Mission District'): 15,
    ('Mission District', 'Financial District'): 17,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Pacific Heights'): 16
}

# Constraints
current_location = 'Financial District'
current_time = time_to_minutes('9:00')

friends = [
    {'name': 'David', 'location': 'Fisherman\'s Wharf', 'start': time_to_minutes('10:45'), 'end': time_to_minutes('15:30'), 'duration': 15},
    {'name': 'Timothy', 'location': 'Pacific Heights', 'start': time_to_minutes('9:00'), 'end': time_to_minutes('15:30'), 'duration': 75},
    {'name': 'Robert', 'location': 'Mission District', 'start': time_to_minutes('12:15'), 'end': time_to_minutes('19:45'), 'duration': 90}
]

def calculate_schedule(order):
    schedule = []
    current_loc = current_location
    current_time_val = current_time
    
    for friend_idx in order:
        friend = friends[friend_idx]
        travel_time = travel_times.get((current_loc, friend['location']), float('inf'))
        arrival_time = current_time_val + travel_time
        
        # Check if we can meet the friend
        start_meeting = max(arrival_time, friend['start'])
        end_meeting = start_meeting + friend['duration']
        
        if end_meeting > friend['end']:
            return None  # Cannot meet this friend
        
        schedule.append({
            'friend_idx': friend_idx,
            'start': start_meeting,
            'end': end_meeting,
            'travel_time': travel_time,
            'from_loc': current_loc,
            'to_loc': friend['location']
        })
        
        current_loc = friend['location']
        current_time_val = end_meeting
    
    return schedule

best_schedule = None
best_meetings = 0
best_end_time = float('inf')

# Try all possible orders of meeting friends
for order in permutations(range(len(friends))):
    schedule = calculate_schedule(order)
    if schedule:
        num_meetings = len(schedule)
        current_end_time = schedule[-1]['end'] if schedule else float('inf')
        
        # Prioritize more meetings, then earlier end time
        if num_meetings > best_meetings:
            best_meetings = num_meetings
            best_schedule = schedule
            best_end_time = current_end_time
        elif num_meetings == best_meetings and current_end_time < best_end_time:
            best_schedule = schedule
            best_end_time = current_end_time

if best_schedule:
    itinerary = []
    for meeting in best_schedule:
        friend = friends[meeting['friend_idx']]
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": minutes_to_time(meeting['start']),
            "end_time": minutes_to_time(meeting['end'])
        })
    
    result = {
        "itinerary": itinerary
    }
else:
    result = {
        "itinerary": []
    }

print(json.dumps(result, indent=2))