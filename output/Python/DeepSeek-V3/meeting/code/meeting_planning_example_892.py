import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Initialize travel times as a dictionary
travel_times = {
    'Marina District': {
        'Bayview': 27,
        'Sunset District': 19,
        'Richmond District': 11,
        'Nob Hill': 12,
        'Chinatown': 15,
        'Haight-Ashbury': 16,
        'North Beach': 11,
        'Russian Hill': 8,
        'Embarcadero': 14
    },
    'Bayview': {
        'Marina District': 27,
        'Sunset District': 23,
        'Richmond District': 25,
        'Nob Hill': 20,
        'Chinatown': 19,
        'Haight-Ashbury': 19,
        'North Beach': 22,
        'Russian Hill': 23,
        'Embarcadero': 19
    },
    'Sunset District': {
        'Marina District': 21,
        'Bayview': 22,
        'Richmond District': 12,
        'Nob Hill': 27,
        'Chinatown': 30,
        'Haight-Ashbury': 15,
        'North Beach': 28,
        'Russian Hill': 24,
        'Embarcadero': 30
    },
    'Richmond District': {
        'Marina District': 9,
        'Bayview': 27,
        'Sunset District': 11,
        'Nob Hill': 17,
        'Chinatown': 20,
        'Haight-Ashbury': 10,
        'North Beach': 17,
        'Russian Hill': 13,
        'Embarcadero': 19
    },
    'Nob Hill': {
        'Marina District': 11,
        'Bayview': 19,
        'Sunset District': 24,
        'Richmond District': 14,
        'Chinatown': 6,
        'Haight-Ashbury': 13,
        'North Beach': 8,
        'Russian Hill': 5,
        'Embarcadero': 9
    },
    'Chinatown': {
        'Marina District': 12,
        'Bayview': 20,
        'Sunset District': 29,
        'Richmond District': 20,
        'Nob Hill': 9,
        'Haight-Ashbury': 19,
        'North Beach': 3,
        'Russian Hill': 7,
        'Embarcadero': 5
    },
    'Haight-Ashbury': {
        'Marina District': 17,
        'Bayview': 18,
        'Sunset District': 15,
        'Richmond District': 10,
        'Nob Hill': 15,
        'Chinatown': 19,
        'North Beach': 19,
        'Russian Hill': 17,
        'Embarcadero': 20
    },
    'North Beach': {
        'Marina District': 9,
        'Bayview': 25,
        'Sunset District': 27,
        'Richmond District': 18,
        'Nob Hill': 7,
        'Chinatown': 6,
        'Haight-Ashbury': 18,
        'Russian Hill': 4,
        'Embarcadero': 6
    },
    'Russian Hill': {
        'Marina District': 7,
        'Bayview': 23,
        'Sunset District': 23,
        'Richmond District': 14,
        'Nob Hill': 5,
        'Chinatown': 9,
        'Haight-Ashbury': 17,
        'North Beach': 5,
        'Embarcadero': 8
    },
    'Embarcadero': {
        'Marina District': 12,
        'Bayview': 21,
        'Sunset District': 30,
        'Richmond District': 21,
        'Nob Hill': 10,
        'Chinatown': 7,
        'Haight-Ashbury': 21,
        'North Beach': 5,
        'Russian Hill': 8
    }
}

# Define friends and their constraints
friends = [
    {'name': 'Charles', 'location': 'Bayview', 'start': '11:30', 'end': '14:30', 'duration': 45},
    {'name': 'Robert', 'location': 'Sunset District', 'start': '16:45', 'end': '21:00', 'duration': 30},
    {'name': 'Karen', 'location': 'Richmond District', 'start': '19:15', 'end': '21:30', 'duration': 60},
    {'name': 'Rebecca', 'location': 'Nob Hill', 'start': '16:15', 'end': '20:30', 'duration': 90},
    {'name': 'Margaret', 'location': 'Chinatown', 'start': '14:15', 'end': '19:45', 'duration': 120},
    {'name': 'Patricia', 'location': 'Haight-Ashbury', 'start': '14:30', 'end': '20:30', 'duration': 45},
    {'name': 'Mark', 'location': 'North Beach', 'start': '14:00', 'end': '18:30', 'duration': 105},
    {'name': 'Melissa', 'location': 'Russian Hill', 'start': '13:00', 'end': '19:45', 'duration': 30},
    {'name': 'Laura', 'location': 'Embarcadero', 'start': '7:45', 'end': '13:15', 'duration': 105}
]

# Initial position
current_location = 'Marina District'
current_time = time_to_minutes('9:00')
itinerary = []

# Sort friends by earliest possible meeting time
friends_sorted = sorted(friends, key=lambda x: time_to_minutes(x['start']))

# Attempt to schedule meetings in order
for friend in friends_sorted:
    start_window = time_to_minutes(friend['start'])
    end_window = time_to_minutes(friend['end'])
    duration = friend['duration']
    
    # Calculate travel time
    travel_time = travel_times[current_location].get(friend['location'], float('inf'))
    
    # Earliest possible start time after travel
    earliest_start = current_time + travel_time
    if earliest_start > end_window:
        continue  # Can't meet this friend
    
    # Latest possible start time to meet duration
    latest_start = end_window - duration
    if latest_start < start_window:
        continue  # Can't meet for required duration
    
    # Determine actual start time
    start_meeting = max(earliest_start, start_window)
    end_meeting = start_meeting + duration
    
    if end_meeting > end_window:
        continue  # Doesn't fit
    
    # Add to itinerary
    itinerary.append({
        'action': 'meet',
        'location': friend['location'],
        'person': friend['name'],
        'start_time': minutes_to_time(start_meeting),
        'end_time': minutes_to_time(end_meeting)
    })
    
    # Update current location and time
    current_location = friend['location']
    current_time = end_meeting

# Output the itinerary
output = {
    'itinerary': itinerary
}

print(json.dumps(output, indent=2))