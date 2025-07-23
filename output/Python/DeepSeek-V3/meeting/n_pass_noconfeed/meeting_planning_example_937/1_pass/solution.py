import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Initialize travel times
travel_times = {
    'Russian Hill': {
        'Sunset District': 23,
        'Union Square': 10,
        'Nob Hill': 5,
        'Marina District': 7,
        'Richmond District': 14,
        'Financial District': 11,
        'Embarcadero': 8,
        'The Castro': 21,
        'Alamo Square': 15,
        'Presidio': 14
    },
    'Sunset District': {
        'Russian Hill': 24,
        'Union Square': 30,
        'Nob Hill': 27,
        'Marina District': 21,
        'Richmond District': 12,
        'Financial District': 30,
        'Embarcadero': 30,
        'The Castro': 17,
        'Alamo Square': 17,
        'Presidio': 16
    },
    'Union Square': {
        'Russian Hill': 13,
        'Sunset District': 27,
        'Nob Hill': 9,
        'Marina District': 18,
        'Richmond District': 20,
        'Financial District': 9,
        'Embarcadero': 11,
        'The Castro': 17,
        'Alamo Square': 15,
        'Presidio': 24
    },
    'Nob Hill': {
        'Russian Hill': 5,
        'Sunset District': 24,
        'Union Square': 7,
        'Marina District': 11,
        'Richmond District': 14,
        'Financial District': 9,
        'Embarcadero': 9,
        'The Castro': 17,
        'Alamo Square': 11,
        'Presidio': 17
    },
    'Marina District': {
        'Russian Hill': 8,
        'Sunset District': 19,
        'Union Square': 16,
        'Nob Hill': 12,
        'Richmond District': 11,
        'Financial District': 17,
        'Embarcadero': 14,
        'The Castro': 22,
        'Alamo Square': 15,
        'Presidio': 10
    },
    'Richmond District': {
        'Russian Hill': 13,
        'Sunset District': 11,
        'Union Square': 21,
        'Nob Hill': 17,
        'Marina District': 9,
        'Financial District': 22,
        'Embarcadero': 19,
        'The Castro': 16,
        'Alamo Square': 13,
        'Presidio': 7
    },
    'Financial District': {
        'Russian Hill': 11,
        'Sunset District': 30,
        'Union Square': 9,
        'Nob Hill': 8,
        'Marina District': 15,
        'Richmond District': 21,
        'Embarcadero': 4,
        'The Castro': 20,
        'Alamo Square': 17,
        'Presidio': 22
    },
    'Embarcadero': {
        'Russian Hill': 8,
        'Sunset District': 30,
        'Union Square': 10,
        'Nob Hill': 10,
        'Marina District': 12,
        'Richmond District': 21,
        'Financial District': 5,
        'The Castro': 25,
        'Alamo Square': 19,
        'Presidio': 20
    },
    'The Castro': {
        'Russian Hill': 18,
        'Sunset District': 17,
        'Union Square': 19,
        'Nob Hill': 16,
        'Marina District': 21,
        'Richmond District': 16,
        'Financial District': 21,
        'Embarcadero': 22,
        'Alamo Square': 8,
        'Presidio': 20
    },
    'Alamo Square': {
        'Russian Hill': 13,
        'Sunset District': 16,
        'Union Square': 14,
        'Nob Hill': 11,
        'Marina District': 15,
        'Richmond District': 11,
        'Financial District': 17,
        'Embarcadero': 16,
        'The Castro': 8,
        'Presidio': 17
    },
    'Presidio': {
        'Russian Hill': 14,
        'Sunset District': 15,
        'Union Square': 22,
        'Nob Hill': 18,
        'Marina District': 11,
        'Richmond District': 7,
        'Financial District': 23,
        'Embarcadero': 20,
        'The Castro': 21,
        'Alamo Square': 19
    }
}

# Initialize friend data
friends = [
    {'name': 'David', 'location': 'Sunset District', 'start': '9:15', 'end': '22:00', 'duration': 15},
    {'name': 'Kenneth', 'location': 'Union Square', 'start': '21:15', 'end': '21:45', 'duration': 15},
    {'name': 'Patricia', 'location': 'Nob Hill', 'start': '15:00', 'end': '19:15', 'duration': 120},
    {'name': 'Mary', 'location': 'Marina District', 'start': '14:45', 'end': '16:45', 'duration': 45},
    {'name': 'Charles', 'location': 'Richmond District', 'start': '17:15', 'end': '21:00', 'duration': 15},
    {'name': 'Joshua', 'location': 'Financial District', 'start': '14:30', 'end': '17:15', 'duration': 90},
    {'name': 'Ronald', 'location': 'Embarcadero', 'start': '18:15', 'end': '20:45', 'duration': 30},
    {'name': 'George', 'location': 'The Castro', 'start': '14:15', 'end': '19:00', 'duration': 105},
    {'name': 'Kimberly', 'location': 'Alamo Square', 'start': '9:00', 'end': '14:30', 'duration': 105},
    {'name': 'William', 'location': 'Presidio', 'start': '7:00', 'end': '12:45', 'duration': 60}
]

current_location = 'Russian Hill'
current_time = time_to_minutes('9:00')
itinerary = []

# Sort friends by earliest possible meeting time
friends_sorted = sorted(friends, key=lambda x: time_to_minutes(x['start']))

for friend in friends_sorted:
    location = friend['location']
    start_time = time_to_minutes(friend['start'])
    end_time = time_to_minutes(friend['end'])
    duration = friend['duration']
    
    # Calculate travel time
    travel_time = travel_times[current_location].get(location, 0)
    
    # Earliest possible arrival time at friend's location
    arrival_time = current_time + travel_time
    
    # Check if we can meet the friend
    if arrival_time <= end_time - duration:
        # Start meeting as soon as possible after arrival and friend's availability
        meeting_start = max(arrival_time, start_time)
        meeting_end = meeting_start + duration
        
        if meeting_end <= end_time:
            itinerary.append({
                'action': 'meet',
                'location': location,
                'person': friend['name'],
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            current_time = meeting_end
            current_location = location

# Output the itinerary
output = {'itinerary': itinerary}
print(json.dumps(output, indent=2))