import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Travel times in minutes (from_location, to_location): time
travel_times = {
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Fisherman\'s Wharf', 'Mission District'): 22,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Bayview'): 26,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Fisherman\'s Wharf'): 22,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Bayview'): 15,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Mission District'): 13
}

# Meeting constraints
meetings = [
    {
        'person': 'Sarah',
        'location': 'Fisherman\'s Wharf',
        'available_start': '14:45',
        'available_end': '17:30',
        'duration': 105
    },
    {
        'person': 'Mary',
        'location': 'Richmond District',
        'available_start': '13:00',
        'available_end': '19:15',
        'duration': 75
    },
    {
        'person': 'Helen',
        'location': 'Mission District',
        'available_start': '21:45',
        'available_end': '22:30',
        'duration': 30
    },
    {
        'person': 'Thomas',
        'location': 'Bayview',
        'available_start': '15:15',
        'available_end': '18:45',
        'duration': 120
    }
]

def calculate_schedule(meeting_order, include_helen=False):
    current_location = 'Haight-Ashbury'
    current_time = time_to_minutes('9:00')
    schedule = []
    
    for meeting_idx in meeting_order:
        meeting = meetings[meeting_idx]
        if meeting['person'] == 'Helen' and not include_helen:
            continue
            
        location = meeting['location']
        travel_time = travel_times[(current_location, location)]
        
        arrival_time = current_time + travel_time
        available_start = time_to_minutes(meeting['available_start'])
        available_end = time_to_minutes(meeting['available_end'])
        duration = meeting['duration']
        
        # Calculate meeting start time
        start_time = max(arrival_time, available_start)
        end_time = start_time + duration
        
        if end_time > available_end:
            return None  # Can't meet this person
        
        schedule.append({
            'action': 'meet',
            'location': location,
            'person': meeting['person'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        
        current_location = location
        current_time = end_time
    
    # Try to add Helen's meeting if requested and not already included
    if include_helen and not any(m['person'] == 'Helen' for m in schedule):
        helen_meeting = next(m for m in meetings if m['person'] == 'Helen')
        location = helen_meeting['location']
        travel_time = travel_times[(current_location, location)]
        
        arrival_time = current_time + travel_time
        available_start = time_to_minutes(helen_meeting['available_start'])
        available_end = time_to_minutes(helen_meeting['available_end'])
        duration = helen_meeting['duration']
        
        start_time = max(arrival_time, available_start)
        end_time = start_time + duration
        
        if end_time <= available_end:
            schedule.append({
                'action': 'meet',
                'location': location,
                'person': helen_meeting['person'],
                'start_time': minutes_to_time(start_time),
                'end_time': minutes_to_time(end_time)
            })
    
    return schedule

def evaluate_schedule(schedule):
    if not schedule:
        return -1
    # Count how many meetings we have
    count = len(schedule)
    # Prefer schedules that meet more people
    return count

# Try all permutations of the three main meetings (Sarah, Mary, Thomas)
main_meeting_indices = [i for i, m in enumerate(meetings) if m['person'] != 'Helen']
best_schedule = None
best_score = -1

# First try to schedule all three main meetings
for order in permutations(main_meeting_indices):
    schedule = calculate_schedule(order, include_helen=False)
    score = evaluate_schedule(schedule)
    if score > best_score:
        best_score = score
        best_schedule = schedule
        if best_score == 3:  # Found all three main meetings
            break

# If we found all three, try to add Helen
if best_score == 3:
    for order in permutations(main_meeting_indices):
        schedule_with_helen = calculate_schedule(order, include_helen=True)
        if len(schedule_with_helen) == 4:  # Found all four meetings
            best_schedule = schedule_with_helen
            break

# Output the best schedule
output = {
    "itinerary": best_schedule
}

print(json.dumps(output, indent=2))