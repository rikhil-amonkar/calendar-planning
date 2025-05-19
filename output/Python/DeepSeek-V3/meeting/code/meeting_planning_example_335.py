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
    'Pacific Heights': {
        'North Beach': 9,
        'Financial District': 13,
        'Alamo Square': 10,
        'Mission District': 15
    },
    'North Beach': {
        'Pacific Heights': 8,
        'Financial District': 8,
        'Alamo Square': 16,
        'Mission District': 18
    },
    'Financial District': {
        'Pacific Heights': 13,
        'North Beach': 7,
        'Alamo Square': 17,
        'Mission District': 17
    },
    'Alamo Square': {
        'Pacific Heights': 10,
        'North Beach': 15,
        'Financial District': 17,
        'Mission District': 10
    },
    'Mission District': {
        'Pacific Heights': 16,
        'North Beach': 17,
        'Financial District': 17,
        'Alamo Square': 11
    }
}

friends = {
    'Helen': {
        'location': 'North Beach',
        'available_start': '9:00',
        'available_end': '17:00',
        'min_duration': 15
    },
    'Kevin': {
        'location': 'Mission District',
        'available_start': '10:45',
        'available_end': '14:45',
        'min_duration': 45
    },
    'Betty': {
        'location': 'Financial District',
        'available_start': '19:00',
        'available_end': '21:45',
        'min_duration': 90
    },
    'Amanda': {
        'location': 'Alamo Square',
        'available_start': '19:45',
        'available_end': '21:00',
        'min_duration': 60
    }
}

# Generate all possible meeting orders (permutations)
meeting_orders = permutations(['Helen', 'Kevin', 'Betty', 'Amanda'])

best_schedule = None
best_meetings = 0

for order in meeting_orders:
    current_time = time_to_minutes('9:00')
    current_location = 'Pacific Heights'
    schedule = []
    valid = True
    meetings = 0
    
    for person in order:
        friend = friends[person]
        location = friend['location']
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time
        
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        min_duration = friend['min_duration']
        
        # Calculate possible meeting window
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + min_duration
        
        if meeting_end > available_end:
            valid = False
            break
        
        schedule.append({
            'action': 'meet',
            'location': location,
            'person': person,
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = location
        meetings += 1
    
    if valid and meetings > best_meetings:
        best_meetings = meetings
        best_schedule = schedule

# If no schedule meets all friends, try subsets
if best_meetings < 4:
    for size in range(3, 0, -1):
        for order in permutations(['Helen', 'Kevin', 'Betty', 'Amanda'], size):
            current_time = time_to_minutes('9:00')
            current_location = 'Pacific Heights'
            schedule = []
            valid = True
            meetings = 0
            
            for person in order:
                friend = friends[person]
                location = friend['location']
                travel_time = travel_times[current_location][location]
                arrival_time = current_time + travel_time
                
                available_start = time_to_minutes(friend['available_start'])
                available_end = time_to_minutes(friend['available_end'])
                min_duration = friend['min_duration']
                
                meeting_start = max(arrival_time, available_start)
                meeting_end = meeting_start + min_duration
                
                if meeting_end > available_end:
                    valid = False
                    break
                
                schedule.append({
                    'action': 'meet',
                    'location': location,
                    'person': person,
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                
                current_time = meeting_end
                current_location = location
                meetings += 1
            
            if valid and meetings > best_meetings:
                best_meetings = meetings
                best_schedule = schedule
        
        if best_schedule is not None:
            break

# Output the best schedule found
output = {
    "itinerary": best_schedule
}

print(json.dumps(output, indent=2))