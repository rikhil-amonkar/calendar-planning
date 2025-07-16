import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input parameters
travel_times = {
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Embarcadero'): 8,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Mission District'): 13,
    ('Nob Hill', 'Embarcadero'): 9,
    ('Mission District', 'Russian Hill'): 15,
    ('Mission District', 'Nob Hill'): 12,
    ('Mission District', 'Embarcadero'): 19,
    ('Embarcadero', 'Russian Hill'): 8,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Mission District'): 20
}

friends = {
    'Patricia': {
        'location': 'Nob Hill',
        'available_start': '18:30',
        'available_end': '21:45',
        'min_duration': 90
    },
    'Ashley': {
        'location': 'Mission District',
        'available_start': '20:30',
        'available_end': '21:15',
        'min_duration': 45
    },
    'Timothy': {
        'location': 'Embarcadero',
        'available_start': '9:45',
        'available_end': '17:45',
        'min_duration': 120
    }
}

current_location = 'Russian Hill'
current_time = time_to_minutes('9:00')

# Generate all possible meeting orders
meeting_orders = permutations(friends.keys())

best_schedule = None
best_meetings = 0

for order in meeting_orders:
    schedule = []
    temp_location = current_location
    temp_time = current_time
    meetings = 0
    
    for person in order:
        friend = friends[person]
        loc = friend['location']
        travel_time = travel_times.get((temp_location, loc), float('inf'))
        arrival_time = temp_time + travel_time
        
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        min_duration = friend['min_duration']
        
        # Calculate possible meeting window
        meeting_start = max(arrival_time, available_start)
        meeting_end = min(meeting_start + min_duration, available_end)
        
        if meeting_end - meeting_start >= min_duration:
            schedule.append({
                'action': 'meet',
                'location': loc,
                'person': person,
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            meetings += 1
            temp_location = loc
            temp_time = meeting_end
    
    if meetings > best_meetings or (meetings == best_meetings and len(schedule) > len(best_schedule)):
        best_meetings = meetings
        best_schedule = schedule

# If no meetings possible with all, try subsets
if best_meetings < len(friends):
    for num in range(len(friends)-1, 0, -1):
        for subset in permutations(friends.keys(), num):
            schedule = []
            temp_location = current_location
            temp_time = current_time
            meetings = 0
            
            for person in subset:
                friend = friends[person]
                loc = friend['location']
                travel_time = travel_times.get((temp_location, loc), float('inf'))
                arrival_time = temp_time + travel_time
                
                available_start = time_to_minutes(friend['available_start'])
                available_end = time_to_minutes(friend['available_end'])
                min_duration = friend['min_duration']
                
                meeting_start = max(arrival_time, available_start)
                meeting_end = min(meeting_start + min_duration, available_end)
                
                if meeting_end - meeting_start >= min_duration:
                    schedule.append({
                        'action': 'meet',
                        'location': loc,
                        'person': person,
                        'start_time': minutes_to_time(meeting_start),
                        'end_time': minutes_to_time(meeting_end)
                    })
                    meetings += 1
                    temp_location = loc
                    temp_time = meeting_end
            
            if meetings > best_meetings or (meetings == best_meetings and len(schedule) > len(best_schedule)):
                best_meetings = meetings
                best_schedule = schedule
                if best_meetings == len(friends):
                    break
        if best_meetings == len(friends):
            break

# Output the best schedule
output = {
    "itinerary": best_schedule
}

print(json.dumps(output, indent=2))