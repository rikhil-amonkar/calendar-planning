import itertools
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define friends with their constraints
friends = [
    {
        'name': 'Sarah',
        'location': 'Sunset District',
        'available_start': 645,  # 10:45 AM
        'available_end': 1140,   # 7:00 PM
        'min_duration': 30
    },
    {
        'name': 'Richard',
        'location': 'Haight-Ashbury',
        'available_start': 705,  # 11:45 AM
        'available_end': 945,    # 3:45 PM
        'min_duration': 90
    },
    {
        'name': 'Elizabeth',
        'location': 'Mission District',
        'available_start': 660,  # 11:00 AM
        'available_end': 1035,   # 5:15 PM
        'min_duration': 120
    },
    {
        'name': 'Michelle',
        'location': 'Golden Gate Park',
        'available_start': 1095, # 6:15 PM
        'available_end': 1245,   # 8:45 PM
        'min_duration': 90
    }
]

# Define travel times between districts
travel_times = {
    'Richmond District': {
        'Sunset District': 11,
        'Haight-Ashbury': 10,
        'Mission District': 20,
        'Golden Gate Park': 9
    },
    'Sunset District': {
        'Richmond District': 12,
        'Haight-Ashbury': 15,
        'Mission District': 24,
        'Golden Gate Park': 11
    },
    'Haight-Ashbury': {
        'Richmond District': 10,
        'Sunset District': 15,
        'Mission District': 11,
        'Golden Gate Park': 7
    },
    'Mission District': {
        'Richmond District': 20,
        'Sunset District': 24,
        'Haight-Ashbury': 12,
        'Golden Gate Park': 17
    },
    'Golden Gate Park': {
        'Richmond District': 7,
        'Sunset District': 10,
        'Haight-Ashbury': 7,
        'Mission District': 17
    }
}

best_itinerary = []
max_count = 0

# Evaluate all permutations of friend visit order
for perm in itertools.permutations(friends):
    current_time = 540  # Start at 9:00 AM (540 minutes)
    current_location = 'Richmond District'
    meetings = []
    
    for friend in perm:
        # Calculate travel time to friend's location
        dest = friend['location']
        travel_time = travel_times[current_location][dest]
        arrival_time = current_time + travel_time
        
        # Check if arrival time exceeds friend's available end time
        if arrival_time > friend['available_end']:
            break
        
        # Determine earliest possible meeting start time
        start = max(arrival_time, friend['available_start'])
        
        # Check if meeting can be completed within friend's availability
        if start + friend['min_duration'] > friend['available_end']:
            break
        
        # Add meeting to itinerary
        meetings.append({
            'friend': friend,
            'start': start,
            'end': start + friend['min_duration']
        })
        
        # Update current time and location
        current_time = start + friend['min_duration']
        current_location = dest
    
    # Update best itinerary if current one is better
    if len(meetings) > max_count:
        max_count = len(meetings)
        best_itinerary = meetings

# Convert best itinerary to required JSON format
itinerary = []
for meeting in best_itinerary:
    friend = meeting['friend']
    itinerary.append({
        'action': 'meet',
        'location': friend['location'],
        'person': friend['name'],
        'start_time': minutes_to_time_str(meeting['start']),
        'end_time': minutes_to_time_str(meeting['end'])
    })

# Output result as JSON
print(json.dumps({'itinerary': itinerary}, indent=2))