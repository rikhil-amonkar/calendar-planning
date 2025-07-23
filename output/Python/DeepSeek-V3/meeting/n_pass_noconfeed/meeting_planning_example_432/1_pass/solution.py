import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Travel times in minutes (from_location, to_location): time
travel_times = {
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Embarcadero'): 8,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Financial District'): 19,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Embarcadero'): 19,
    ('Mission District', 'Financial District'): 17,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Fisherman\'s Wharf'): 6,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Mission District'): 20,
    ('Embarcadero', 'Financial District'): 5,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Mission District'): 17,
    ('Financial District', 'Embarcadero'): 4
}

# Meeting constraints
meetings = [
    {
        'person': 'Joseph',
        'location': 'Fisherman\'s Wharf',
        'available_start': '8:00',
        'available_end': '17:30',
        'duration': 90
    },
    {
        'person': 'Jeffrey',
        'location': 'Bayview',
        'available_start': '17:30',
        'available_end': '21:30',
        'duration': 60
    },
    {
        'person': 'Kevin',
        'location': 'Mission District',
        'available_start': '11:15',
        'available_end': '15:15',
        'duration': 30
    },
    {
        'person': 'David',
        'location': 'Embarcadero',
        'available_start': '8:15',
        'available_end': '9:00',
        'duration': 30
    },
    {
        'person': 'Barbara',
        'location': 'Financial District',
        'available_start': '10:30',
        'available_end': '16:30',
        'duration': 15
    }
]

def generate_schedule(order):
    current_time = time_to_minutes('9:00')
    current_location = 'Golden Gate Park'
    schedule = []
    
    for meeting_idx in order:
        meeting = meetings[meeting_idx]
        travel_time = travel_times[(current_location, meeting['location'])]
        arrival_time = current_time + travel_time
        available_start = time_to_minutes(meeting['available_start'])
        available_end = time_to_minutes(meeting['available_end'])
        
        # Check if we can arrive before available_end
        if arrival_time >= available_end:
            return None
        
        # Start time is max of arrival_time and available_start
        start_time = max(arrival_time, available_start)
        end_time = start_time + meeting['duration']
        
        if end_time > available_end:
            return None
        
        schedule.append({
            'action': 'meet',
            'location': meeting['location'],
            'person': meeting['person'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        
        current_time = end_time
        current_location = meeting['location']
    
    return schedule

def evaluate_schedule(schedule):
    if not schedule:
        return -1
    # Count number of meetings
    return len(schedule)

best_schedule = None
best_score = -1

# Try all possible orders of meetings (permutations)
for order in permutations(range(len(meetings))):
    schedule = generate_schedule(order)
    score = evaluate_schedule(schedule)
    if score > best_score:
        best_score = score
        best_schedule = schedule

# Ensure we meet Jeffrey last since his time is in the evening
if best_schedule:
    # Find Jeffrey's meeting
    jeffrey_idx = None
    for i, item in enumerate(best_schedule):
        if item['person'] == 'Jeffrey':
            jeffrey_idx = i
            break
    
    if jeffrey_idx is not None and jeffrey_idx != len(best_schedule) - 1:
        # Move Jeffrey to the end
        jeffrey_meeting = best_schedule.pop(jeffrey_idx)
        best_schedule.append(jeffrey_meeting)
        
        # Recalculate times
        current_time = time_to_minutes('9:00')
        current_location = 'Golden Gate Park'
        new_schedule = []
        
        for meeting in best_schedule:
            travel_time = travel_times[(current_location, meeting['location'])]
            arrival_time = current_time + travel_time
            available_start = time_to_minutes(meeting['start_time'].split(' ')[0])
            available_end = time_to_minutes(meeting['end_time'].split(' ')[0])
            
            # Start time is max of arrival_time and available_start
            start_time = max(arrival_time, available_start)
            end_time = start_time + time_to_minutes(meeting['end_time']) - time_to_minutes(meeting['start_time'])
            
            new_schedule.append({
                'action': 'meet',
                'location': meeting['location'],
                'person': meeting['person'],
                'start_time': minutes_to_time(start_time),
                'end_time': minutes_to_time(end_time)
            })
            
            current_time = end_time
            current_location = meeting['location']
        
        best_schedule = new_schedule

output = {
    "itinerary": best_schedule if best_schedule else []
}

print(json.dumps(output, indent=2))