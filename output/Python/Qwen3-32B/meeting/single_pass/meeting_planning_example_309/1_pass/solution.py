import itertools
import json

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m}"

# Travel times between locations
travel_times = {
    'Financial District': {
        'Chinatown': 5,
        'Alamo Square': 17,
        'Bayview': 19,
        "Fisherman's Wharf": 10
    },
    'Chinatown': {
        'Financial District': 5,
        'Alamo Square': 17,
        'Bayview': 22,
        "Fisherman's Wharf": 8
    },
    'Alamo Square': {
        'Financial District': 17,
        'Chinatown': 16,
        'Bayview': 16,
        "Fisherman's Wharf": 19
    },
    'Bayview': {
        'Financial District': 19,
        'Chinatown': 18,
        'Alamo Square': 16,
        "Fisherman's Wharf": 25
    },
    "Fisherman's Wharf": {
        'Financial District': 11,
        'Chinatown': 12,
        'Alamo Square': 20,
        'Bayview': 26
    }
}

# Friend constraints
friends = [
    {
        'name': 'Nancy',
        'location': 'Chinatown',
        'available_start': '9:30',
        'available_end': '13:30',
        'required_duration': 90
    },
    {
        'name': 'Mary',
        'location': 'Alamo Square',
        'available_start': '7:00',
        'available_end': '21:00',
        'required_duration': 75
    },
    {
        'name': 'Jessica',
        'location': 'Bayview',
        'available_start': '11:15',
        'available_end': '13:45',
        'required_duration': 45
    }
]

best_itinerary = []
max_friends = 0

# Starting time and location
start_time_minutes = 9 * 60  # 9:00 AM
start_location = 'Financial District'

# Check all permutations of friends
for perm in itertools.permutations(friends):
    current_time = start_time_minutes
    current_location = start_location
    itinerary = []
    valid = True
    
    for friend in perm:
        destination = friend['location']
        travel_time = travel_times[current_location][destination]
        arrival_time = current_time + travel_time
        
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        required_duration = friend['required_duration']
        
        # Calculate meeting start time
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + required_duration
        
        if meeting_end > available_end:
            valid = False
            break
        
        # Add to itinerary
        itinerary.append({
            'friend': friend,
            'start': meeting_start,
            'end': meeting_end
        })
        
        # Update current time and location
        current_time = meeting_end
        current_location = destination
    
    if valid and len(itinerary) > max_friends:
        max_friends = len(itinerary)
        best_itinerary = itinerary

# Format result as JSON
result = {"itinerary": []}
for meeting in best_itinerary:
    friend = meeting['friend']
    result["itinerary"].append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": minutes_to_time(meeting['start']),
        "end_time": minutes_to_time(meeting['end'])
    })

print(json.dumps(result, indent=2))