import itertools
import json

def time_str_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

friends = [
    {
        'name': 'Melissa',
        'location': 'Golden Gate Park',
        'available_start': '8:30',
        'available_end': '20:00',
        'required_duration': 15
    },
    {
        'name': 'Nancy',
        'location': 'Presidio',
        'available_start': '19:45',
        'available_end': '22:00',
        'required_duration': 105
    },
    {
        'name': 'Emily',
        'location': 'Richmond District',
        'available_start': '16:45',
        'available_end': '22:00',
        'required_duration': 120
    }
]

travel_times = {
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
    ('Fisherman\'s Wharf', 'Richmond District'): 18,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Richmond District'): 7,
    ('Richmond District', 'Fisherman\'s Wharf'): 18,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Presidio'): 7,
}

best_itinerary = None
max_friends = 0

for perm in itertools.permutations(friends):
    current_time = 9 * 60  # 9:00 AM in minutes
    current_location = "Fisherman's Wharf"
    valid = True
    itinerary = []
    
    for friend in perm:
        from_loc = current_location
        to_loc = friend['location']
        
        # Get travel time
        travel_time = travel_times.get((from_loc, to_loc))
        if travel_time is None:
            valid = False
            break
        
        arrival_time = current_time + travel_time
        
        # Friend's availability
        friend_start = time_str_to_minutes(friend['available_start'])
        friend_end = time_str_to_minutes(friend['available_end'])
        required = friend['required_duration']
        
        # Calculate latest possible start time for the meeting
        latest_start = friend_end - required
        
        if arrival_time > latest_start:
            valid = False
            break
        
        # Determine actual meeting start time
        meeting_start = max(arrival_time, friend_start)
        meeting_end = meeting_start + required
        
        # Add to itinerary
        itinerary.append({
            'action': 'meet',
            'location': to_loc,
            'person': friend['name'],
            'start_time': minutes_to_time_str(meeting_start),
            'end_time': minutes_to_time_str(meeting_end)
        })
        
        # Update current time and location
        current_time = meeting_end
        current_location = to_loc
    
    if valid and len(itinerary) > max_friends:
        best_itinerary = itinerary
        max_friends = len(itinerary)

# Output the best itinerary as JSON
result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))