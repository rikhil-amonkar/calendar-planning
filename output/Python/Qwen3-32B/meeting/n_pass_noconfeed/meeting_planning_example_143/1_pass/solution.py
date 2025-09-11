import itertools
import json

def time_to_minutes(t_str):
    h, m = map(int, t_str.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times between locations in minutes
travel_times = {
    'North Beach': {'Pacific Heights': 8, 'Embarcadero': 6},
    'Pacific Heights': {'North Beach': 9, 'Embarcadero': 10},
    'Embarcadero': {'North Beach': 5, 'Pacific Heights': 11},
}

# Friend meeting constraints
friends = [
    {
        'name': 'Mark',
        'location': 'Embarcadero',
        'available_start': time_to_minutes('13:00'),
        'available_end': time_to_minutes('17:45'),
        'required_duration': 120
    },
    {
        'name': 'Karen',
        'location': 'Pacific Heights',
        'available_start': time_to_minutes('18:45'),
        'available_end': time_to_minutes('20:15'),
        'required_duration': 90
    }
]

# Starting conditions
start_time_minutes = time_to_minutes('9:00')
start_location = 'North Beach'

best_schedule = []
max_friends = 0

# Check all permutations of friend visit order
for perm in itertools.permutations(friends):
    schedule = []
    current_time = start_time_minutes
    current_loc = start_location
    valid = True
    
    for friend in perm:
        # Calculate travel time to friend's location
        try:
            travel_time = travel_times[current_loc][friend['location']]
        except KeyError:
            valid = False
            break
            
        arrival_time = current_time + travel_time
        
        # Determine if meeting is possible
        earliest_start = max(arrival_time, friend['available_start'])
        latest_start = friend['available_end'] - friend['required_duration']
        
        if earliest_start > latest_start:
            valid = False
            break
            
        # Schedule the meeting
        meeting_start = earliest_start
        meeting_end = meeting_start + friend['required_duration']
        
        schedule.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        # Update current time and location
        current_time = meeting_end
        current_loc = friend['location']
    
    # Update best schedule if valid and better
    if valid and len(schedule) > max_friends:
        max_friends = len(schedule)
        best_schedule = schedule

# Output result in required JSON format
result = {"itinerary": best_schedule}
print(json.dumps(result, indent=2))