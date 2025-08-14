import itertools
import json

def convert_minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define friends with their data
friends = [
    {
        'name': 'Mark',
        'location': 'Russian Hill',
        'start_time': 600,  # 10:00 AM
        'end_time': 1275,   # 9:15 PM
        'duration': 75
    },
    {
        'name': 'William',
        'location': 'Mission District',
        'start_time': 795,  # 1:15 PM
        'end_time': 1170,   # 7:30 PM
        'duration': 30
    },
    {
        'name': 'Robert',
        'location': 'Golden Gate Park',
        'start_time': 855,  # 2:15 PM
        'end_time': 1290,   # 9:30 PM
        'duration': 45
    },
    {
        'name': 'Linda',
        'location': 'Sunset District',
        'start_time': 930,  # 3:30 PM
        'end_time': 1185,   # 7:45 PM
        'duration': 30
    },
    {
        'name': 'Elizabeth',
        'location': 'Haight-Ashbury',
        'start_time': 1035, # 5:15 PM
        'end_time': 1170,   # 7:30 PM
        'duration': 105
    },
    {
        'name': 'Rebecca',
        'location': 'Presidio',
        'start_time': 1095, # 6:15 PM
        'end_time': 1245,   # 8:45 PM
        'duration': 60
    }
]

# Define travel times between locations
travel_times = {
    'Castro': {
        'Presidio': 20,
        'Sunset District': 17,
        'Haight-Ashbury': 6,
        'Mission District': 7,
        'Golden Gate Park': 11,
        'Russian Hill': 18,
    },
    'Presidio': {
        'Castro': 21,
        'Sunset District': 15,
        'Haight-Ashbury': 15,
        'Mission District': 26,
        'Golden Gate Park': 12,
        'Russian Hill': 14,
    },
    'Sunset District': {
        'Castro': 17,
        'Presidio': 16,
        'Haight-Ashbury': 15,
        'Mission District': 24,
        'Golden Gate Park': 11,
        'Russian Hill': 24,
    },
    'Haight-Ashbury': {
        'Castro': 6,
        'Presidio': 15,
        'Sunset District': 15,
        'Mission District': 11,
        'Golden Gate Park': 7,
        'Russian Hill': 17,
    },
    'Mission District': {
        'Castro': 7,
        'Presidio': 25,
        'Sunset District': 24,
        'Haight-Ashbury': 12,
        'Golden Gate Park': 17,
        'Russian Hill': 15,
    },
    'Golden Gate Park': {
        'Castro': 13,
        'Presidio': 11,
        'Sunset District': 10,
        'Haight-Ashbury': 7,
        'Mission District': 17,
        'Russian Hill': 19,
    },
    'Russian Hill': {
        'Castro': 21,
        'Presidio': 14,
        'Sunset District': 23,
        'Haight-Ashbury': 17,
        'Mission District': 16,
        'Golden Gate Park': 21,
    },
}

best_schedule = []
max_friends = 0

# Check all possible permutations of friends
for r in range(1, len(friends) + 1):
    for perm in itertools.permutations(friends, r):
        current_time = 540  # Start at 9:00 AM at Castro
        current_location = 'Castro'
        valid = True
        schedule = []
        
        for friend in perm:
            # Calculate travel time to this friend's location
            travel_time = travel_times[current_location][friend['location']]
            arrival_time = current_time + travel_time
            
            # Determine earliest start time for the meeting
            start_time = max(arrival_time, friend['start_time'])
            
            # Check if the meeting can fit within the friend's availability
            if start_time + friend['duration'] > friend['end_time']:
                valid = False
                break
            
            # Record the meeting
            schedule.append({
                'name': friend['name'],
                'location': friend['location'],
                'start_time': start_time,
                'end_time': start_time + friend['duration']
            })
            
            # Update current time and location
            current_time = start_time + friend['duration']
            current_location = friend['location']
        
        if valid:
            if len(perm) > max_friends:
                max_friends = len(perm)
                best_schedule = schedule
            elif len(perm) == max_friends and max_friends > 0:
                # Optional: choose the one with earliest end time, but for simplicity, keep the first one
                pass

# Convert best schedule to the required JSON format
itinerary = []
for meeting in best_schedule:
    start_time = convert_minutes_to_time(meeting['start_time'])
    end_time = convert_minutes_to_time(meeting['end_time'])
    itinerary.append({
        "action": "meet",
        "location": meeting['location'],
        "person": meeting['name'],
        "start_time": start_time,
        "end_time": end_time
    })

result = {"itinerary": itinerary}

print(json.dumps(result, indent=2))