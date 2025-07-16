import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input data
travel_times = {
    'Fisherman\'s Wharf': {
        'The Castro': 26,
        'Golden Gate Park': 25,
        'Embarcadero': 8,
        'Russian Hill': 7,
        'Nob Hill': 11,
        'Alamo Square': 20,
        'North Beach': 6
    },
    'The Castro': {
        'Fisherman\'s Wharf': 24,
        'Golden Gate Park': 11,
        'Embarcadero': 22,
        'Russian Hill': 18,
        'Nob Hill': 16,
        'Alamo Square': 8,
        'North Beach': 20
    },
    'Golden Gate Park': {
        'Fisherman\'s Wharf': 24,
        'The Castro': 13,
        'Embarcadero': 25,
        'Russian Hill': 19,
        'Nob Hill': 20,
        'Alamo Square': 10,
        'North Beach': 24
    },
    'Embarcadero': {
        'Fisherman\'s Wharf': 6,
        'The Castro': 25,
        'Golden Gate Park': 25,
        'Russian Hill': 8,
        'Nob Hill': 10,
        'Alamo Square': 19,
        'North Beach': 5
    },
    'Russian Hill': {
        'Fisherman\'s Wharf': 7,
        'The Castro': 21,
        'Golden Gate Park': 21,
        'Embarcadero': 8,
        'Nob Hill': 5,
        'Alamo Square': 15,
        'North Beach': 5
    },
    'Nob Hill': {
        'Fisherman\'s Wharf': 11,
        'The Castro': 17,
        'Golden Gate Park': 17,
        'Embarcadero': 9,
        'Russian Hill': 5,
        'Alamo Square': 11,
        'North Beach': 8
    },
    'Alamo Square': {
        'Fisherman\'s Wharf': 19,
        'The Castro': 8,
        'Golden Gate Park': 9,
        'Embarcadero': 17,
        'Russian Hill': 13,
        'Nob Hill': 11,
        'North Beach': 15
    },
    'North Beach': {
        'Fisherman\'s Wharf': 5,
        'The Castro': 22,
        'Golden Gate Park': 22,
        'Embarcadero': 6,
        'Russian Hill': 4,
        'Nob Hill': 7,
        'Alamo Square': 16
    }
}

friends = [
    {'name': 'Laura', 'location': 'The Castro', 'start': '19:45', 'end': '21:30', 'min_duration': 105},
    {'name': 'Daniel', 'location': 'Golden Gate Park', 'start': '21:15', 'end': '21:45', 'min_duration': 15},
    {'name': 'William', 'location': 'Embarcadero', 'start': '7:00', 'end': '9:00', 'min_duration': 90},
    {'name': 'Karen', 'location': 'Russian Hill', 'start': '14:30', 'end': '19:45', 'min_duration': 30},
    {'name': 'Stephanie', 'location': 'Nob Hill', 'start': '7:30', 'end': '9:30', 'min_duration': 45},
    {'name': 'Joseph', 'location': 'Alamo Square', 'start': '11:30', 'end': '12:45', 'min_duration': 15},
    {'name': 'Kimberly', 'location': 'North Beach', 'start': '15:45', 'end': '19:15', 'min_duration': 30}
]

current_time = time_to_minutes('9:00')
current_location = 'Fisherman\'s Wharf'
itinerary = []

# Helper function to check if a meeting is possible
def can_meet(friend, arrival_time):
    start = time_to_minutes(friend['start'])
    end = time_to_minutes(friend['end'])
    if arrival_time >= end:
        return False
    available_duration = end - max(arrival_time, start)
    return available_duration >= friend['min_duration']

# Process meetings in priority order (earlier meetings first)
friends_sorted = sorted(friends, key=lambda x: time_to_minutes(x['start']))

for friend in friends_sorted:
    travel_time = travel_times[current_location][friend['location']]
    arrival_time = current_time + travel_time
    
    if can_meet(friend, arrival_time):
        start_time = max(arrival_time, time_to_minutes(friend['start']))
        end_time = start_time + friend['min_duration']
        
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(start_time),
            'end_time': minutes_to_time(end_time)
        })
        
        current_time = end_time
        current_location = friend['location']

# Output the result
output = {'itinerary': itinerary}
print(json.dumps(output, indent=2))