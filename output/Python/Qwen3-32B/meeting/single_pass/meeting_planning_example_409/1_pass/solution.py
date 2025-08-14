import itertools
import json

def convert_time(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define travel times between locations
travel_times = {
    'Fisherman\'s Wharf': {
        'Bayview': 26,
        'Golden Gate Park': 25,
        'Nob Hill': 11,
        'Marina District': 9,
        'Embarcadero': 8
    },
    'Bayview': {
        'Fisherman\'s Wharf': 25,
        'Golden Gate Park': 22,
        'Nob Hill': 20,
        'Marina District': 25,
        'Embarcadero': 19
    },
    'Golden Gate Park': {
        'Fisherman\'s Wharf': 24,
        'Bayview': 23,
        'Nob Hill': 20,
        'Marina District': 16,
        'Embarcadero': 25
    },
    'Nob Hill': {
        'Fisherman\'s Wharf': 11,
        'Bayview': 19,
        'Golden Gate Park': 17,
        'Marina District': 11,
        'Embarcadero': 9
    },
    'Marina District': {
        'Fisherman\'s Wharf': 10,
        'Bayview': 27,
        'Golden Gate Park': 18,
        'Nob Hill': 12,
        'Embarcadero': 14
    },
    'Embarcadero': {
        'Fisherman\'s Wharf': 6,
        'Bayview': 21,
        'Golden Gate Park': 25,
        'Nob Hill': 10,
        'Marina District': 12
    }
}

# Define friends with their constraints
friends = [
    {
        'name': 'Laura',
        'location': 'Nob Hill',
        'available_start': convert_time('8:45'),
        'available_end': convert_time('16:15'),
        'required_duration': 30
    },
    {
        'name': 'Thomas',
        'location': 'Bayview',
        'available_start': convert_time('15:30'),
        'available_end': convert_time('18:30'),
        'required_duration': 120
    },
    {
        'name': 'Patricia',
        'location': 'Embarcadero',
        'available_start': convert_time('17:30'),
        'available_end': convert_time('22:00'),
        'required_duration': 45
    },
    {
        'name': 'Betty',
        'location': 'Marina District',
        'available_start': convert_time('18:45'),
        'available_end': convert_time('21:45'),
        'required_duration': 45
    },
    {
        'name': 'Stephanie',
        'location': 'Golden Gate Park',
        'available_start': convert_time('18:30'),
        'available_end': convert_time('21:45'),
        'required_duration': 30
    }
]

# Starting conditions
start_time = convert_time('9:00')
start_location = 'Fisherman\'s Wharf'

best_itinerary = []
max_friends = 0

# Try all permutations of friends
for perm in itertools.permutations(friends):
    current_time = start_time
    current_location = start_location
    itinerary = []
    valid = True
    
    for friend in perm:
        # Calculate travel time to friend's location
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        
        # Determine earliest and latest possible meeting start times
        earliest_start = max(arrival_time, friend['available_start'])
        latest_start = friend['available_end'] - friend['required_duration']
        
        if earliest_start > latest_start:
            valid = False
            break
            
        # Schedule meeting at earliest possible time
        meeting_start = earliest_start
        meeting_end = meeting_start + friend['required_duration']
        
        # Add to itinerary
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': format_time(meeting_start),
            'end_time': format_time(meeting_end)
        })
        
        # Update for next iteration
        current_time = meeting_end
        current_location = friend['location']
    
    if valid and len(itinerary) > max_friends:
        max_friends = len(itinerary)
        best_itinerary = itinerary
    elif valid and len(itinerary) == max_friends:
        # Tiebreaker: choose itinerary that ends earliest
        if best_itinerary:
            current_end = current_time
            best_end = convert_time(best_itinerary[-1]['end_time'])
            if current_end < best_end:
                best_itinerary = itinerary

# Output result as JSON
result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))