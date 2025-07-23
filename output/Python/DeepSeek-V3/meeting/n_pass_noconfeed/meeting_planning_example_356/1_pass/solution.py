import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Input parameters
travel_times = {
    'Bayview': {
        'North Beach': 21,
        'Presidio': 31,
        'Haight-Ashbury': 19,
        'Union Square': 17
    },
    'North Beach': {
        'Bayview': 22,
        'Presidio': 17,
        'Haight-Ashbury': 18,
        'Union Square': 7
    },
    'Presidio': {
        'Bayview': 31,
        'North Beach': 18,
        'Haight-Ashbury': 15,
        'Union Square': 22
    },
    'Haight-Ashbury': {
        'Bayview': 18,
        'North Beach': 19,
        'Presidio': 15,
        'Union Square': 17
    },
    'Union Square': {
        'Bayview': 15,
        'North Beach': 10,
        'Presidio': 24,
        'Haight-Ashbury': 18
    }
}

friends = [
    {
        'name': 'Barbara',
        'location': 'North Beach',
        'available_start': '13:45',
        'available_end': '20:15',
        'min_duration': 60
    },
    {
        'name': 'Margaret',
        'location': 'Presidio',
        'available_start': '10:15',
        'available_end': '15:15',
        'min_duration': 30
    },
    {
        'name': 'Kevin',
        'location': 'Haight-Ashbury',
        'available_start': '20:00',
        'available_end': '20:45',
        'min_duration': 30
    },
    {
        'name': 'Kimberly',
        'location': 'Union Square',
        'available_start': '7:45',
        'available_end': '16:45',
        'min_duration': 30
    }
]

# Initial conditions
current_location = 'Bayview'
current_time = time_to_minutes('9:00')

# Generate all possible permutations of friends
friend_permutations = permutations(friends)

best_itinerary = []
max_meetings = 0

for perm in friend_permutations:
    itinerary = []
    temp_location = current_location
    temp_time = current_time
    meetings = 0
    
    for friend in perm:
        # Check if we can meet this friend
        travel_time = travel_times[temp_location][friend['location']]
        arrival_time = temp_time + travel_time
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        
        # Calculate possible meeting window
        meeting_start = max(arrival_time, available_start)
        meeting_end = min(meeting_start + friend['min_duration'], available_end)
        
        if meeting_end - meeting_start >= friend['min_duration']:
            # Can meet this friend
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            meetings += 1
            temp_location = friend['location']
            temp_time = meeting_end
        else:
            # Can't meet this friend, skip
            continue
    
    if meetings > max_meetings:
        max_meetings = meetings
        best_itinerary = itinerary
    elif meetings == max_meetings and len(itinerary) > 0:
        # Prefer itineraries that end earlier
        if time_to_minutes(itinerary[-1]['end_time']) < time_to_minutes(best_itinerary[-1]['end_time']):
            best_itinerary = itinerary

# Output the result
output = {
    "itinerary": best_itinerary
}

print(json.dumps(output, indent=2))