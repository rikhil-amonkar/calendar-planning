import itertools
import json

# Travel times in minutes between locations
travel_times = {
    'Sunset District': {
        'Russian Hill': 24,
        'The Castro': 17,
        'Richmond District': 12,
        'Marina District': 21,
        'North Beach': 29,
        'Union Square': 30,
        'Golden Gate Park': 11,
    },
    'Russian Hill': {
        'Sunset District': 23,
        'The Castro': 21,
        'Richmond District': 14,
        'Marina District': 7,
        'North Beach': 5,
        'Union Square': 11,
        'Golden Gate Park': 21,
    },
    'The Castro': {
        'Sunset District': 17,
        'Russian Hill': 18,
        'Richmond District': 16,
        'Marina District': 21,
        'North Beach': 20,
        'Union Square': 19,
        'Golden Gate Park': 11,
    },
    'Richmond District': {
        'Sunset District': 11,
        'Russian Hill': 13,
        'The Castro': 16,
        'Marina District': 9,
        'North Beach': 17,
        'Union Square': 21,
        'Golden Gate Park': 9,
    },
    'Marina District': {
        'Sunset District': 19,
        'Russian Hill': 8,
        'The Castro': 22,
        'Richmond District': 11,
        'North Beach': 11,
        'Union Square': 16,
        'Golden Gate Park': 18,
    },
    'North Beach': {
        'Sunset District': 27,
        'Russian Hill': 4,
        'The Castro': 22,
        'Richmond District': 18,
        'Marina District': 9,
        'Union Square': 7,
        'Golden Gate Park': 22,
    },
    'Union Square': {
        'Sunset District': 26,
        'Russian Hill': 13,
        'The Castro': 19,
        'Richmond District': 20,
        'Marina District': 18,
        'North Beach': 10,
        'Golden Gate Park': 22,
    },
    'Golden Gate Park': {
        'Sunset District': 10,
        'Russian Hill': 19,
        'The Castro': 13,
        'Richmond District': 7,
        'Marina District': 16,
        'North Beach': 24,
        'Union Square': 22,
    }
}

# Friends' data
friends = [
    {
        'name': 'Karen',
        'location': 'Russian Hill',
        'start': '20:45',
        'end': '21:45',
        'duration': 60,
    },
    {
        'name': 'Jessica',
        'location': 'The Castro',
        'start': '15:45',
        'end': '19:30',
        'duration': 60,
    },
    {
        'name': 'Matthew',
        'location': 'Richmond District',
        'start': '7:30',
        'end': '15:15',
        'duration': 15,
    },
    {
        'name': 'Michelle',
        'location': 'Marina District',
        'start': '10:30',
        'end': '18:45',
        'duration': 75,
    },
    {
        'name': 'Carol',
        'location': 'North Beach',
        'start': '12:00',
        'end': '17:00',
        'duration': 90,
    },
    {
        'name': 'Stephanie',
        'location': 'Union Square',
        'start': '10:45',
        'end': '14:15',
        'duration': 30,
    },
    {
        'name': 'Linda',
        'location': 'Golden Gate Park',
        'start': '10:45',
        'end': '22:00',
        'duration': 90,
    },
]

best_itinerary = []

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Try all possible permutations of friends
for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM in minutes
    current_location = 'Sunset District'
    temp_itinerary = []
    
    for friend in perm:
        # Convert friend's time window to minutes
        start = time_to_minutes(friend['start'])
        end = time_to_minutes(friend['end'])
        
        # Get travel time from current_location to friend's location
        if current_location not in travel_times or friend['location'] not in travel_times[current_location]:
            break  # No path available
        
        travel = travel_times[current_location][friend['location']]
        arrival = current_time + travel
        
        # Determine meeting start time
        meeting_start = max(arrival, start)
        meeting_end = meeting_start + friend['duration']
        
        if meeting_end > end:
            break  # Cannot meet this friend
        
        # Add to temporary itinerary
        temp_itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        # Update current time and location
        current_time = meeting_end
        current_location = friend['location']
    
    # Update best itinerary if this permutation is better
    if len(temp_itinerary) > len(best_itinerary):
        best_itinerary = temp_itinerary

# Prepare the result
result = {
    "itinerary": best_itinerary
}

# Print the result as JSON
print(json.dumps(result))