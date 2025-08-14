import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

# Travel times between locations
travel_times = {
    'Sunset District': {
        'Chinatown': 30,
        'Russian Hill': 24,
        'North Beach': 29
    },
    'Chinatown': {
        'Sunset District': 29,
        'Russian Hill': 7,
        'North Beach': 3
    },
    'Russian Hill': {
        'Sunset District': 23,
        'Chinatown': 9,
        'North Beach': 5
    },
    'North Beach': {
        'Sunset District': 27,
        'Chinatown': 6,
        'Russian Hill': 4
    }
}

# Friend constraints
friends = [
    {
        'name': 'Melissa',
        'location': 'North Beach',
        'available_start': time_to_minutes('8:15'),
        'available_end': time_to_minutes('13:30'),
        'required_duration': 105
    },
    {
        'name': 'Anthony',
        'location': 'Chinatown',
        'available_start': time_to_minutes('13:15'),
        'available_end': time_to_minutes('14:30'),
        'required_duration': 60
    },
    {
        'name': 'Rebecca',
        'location': 'Russian Hill',
        'available_start': time_to_minutes('19:30'),
        'available_end': time_to_minutes('21:15'),
        'required_duration': 105
    }
]

# Initial conditions
start_location = 'Sunset District'
start_time = time_to_minutes('9:00')

best_itinerary = []
max_met = 0

# Check all permutations of friends
for perm in itertools.permutations(friends):
    current_time = start_time
    current_location = start_location
    itinerary = []
    met_count = 0
    
    for friend in perm:
        # Calculate travel time
        dest = friend['location']
        travel_time = travel_times[current_location][dest]
        current_time += travel_time
        
        # Check if arrival allows meeting
        latest_start = friend['available_end'] - friend['required_duration']
        if current_time > latest_start:
            break
            
        # Determine actual start time
        start_time_meeting = max(current_time, friend['available_start'])
        
        # Check if meeting can occur
        if start_time_meeting + friend['required_duration'] > friend['available_end']:
            break
            
        # Add to itinerary
        end_time_meeting = start_time_meeting + friend['required_duration']
        itinerary.append({
            'action': 'meet',
            'location': dest,
            'person': friend['name'],
            'start_time': minutes_to_time(start_time_meeting),
            'end_time': minutes_to_time(end_time_meeting)
        })
        current_time = end_time_meeting
        current_location = dest
        met_count += 1
    
    # Update best itinerary if this one is better
    if met_count > max_met:
        best_itinerary = itinerary
        max_met = met_count

# Output result
result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))