import itertools
import json

# Travel times in minutes between locations
travel_times = {
    'Financial District': {
        'Fisherman\'s Wharf': 10,
        'Presidio': 22,
        'Bayview': 19,
        'Haight-Ashbury': 19,
        'Russian Hill': 11,
        'The Castro': 20,
        'Marina District': 15,
        'Richmond District': 21,
        'Union Square': 9,
        'Sunset District': 30,
    },
    'Fisherman\'s Wharf': {
        'Financial District': 11,
        'Presidio': 17,
        'Bayview': 26,
        'Haight-Ashbury': 22,
        'Russian Hill': 7,
        'The Castro': 27,
        'Marina District': 9,
        'Richmond District': 18,
        'Union Square': 13,
        'Sunset District': 27,
    },
    'Presidio': {
        'Financial District': 23,
        'Fisherman\'s Wharf': 19,
        'Bayview': 31,
        'Haight-Ashbury': 15,
        'Russian Hill': 14,
        'The Castro': 21,
        'Marina District': 11,
        'Richmond District': 7,
        'Union Square': 22,
        'Sunset District': 15,
    },
    'Bayview': {
        'Financial District': 19,
        'Fisherman\'s Wharf': 25,
        'Presidio': 32,
        'Haight-Ashbury': 19,
        'Russian Hill': 23,
        'The Castro': 19,
        'Marina District': 27,
        'Richmond District': 25,
        'Union Square': 18,
        'Sunset District': 23,
    },
    'Haight-Ashbury': {
        'Financial District': 21,
        'Fisherman\'s Wharf': 23,
        'Presidio': 15,
        'Bayview': 18,
        'Russian Hill': 17,
        'The Castro': 6,
        'Marina District': 17,
        'Richmond District': 10,
        'Union Square': 19,
        'Sunset District': 15,
    },
    'Russian Hill': {
        'Financial District': 11,
        'Fisherman\'s Wharf': 7,
        'Presidio': 14,
        'Bayview': 23,
        'Haight-Ashbury': 17,
        'The Castro': 21,
        'Marina District': 7,
        'Richmond District': 14,
        'Union Square': 10,
        'Sunset District': 23,
    },
    'The Castro': {
        'Financial District': 21,
        'Fisherman\'s Wharf': 24,
        'Presidio': 20,
        'Bayview': 19,
        'Haight-Ashbury': 6,
        'Russian Hill': 18,
        'Marina District': 21,
        'Richmond District': 16,
        'Union Square': 19,
        'Sunset District': 17,
    },
    'Marina District': {
        'Financial District': 17,
        'Fisherman\'s Wharf': 10,
        'Presidio': 10,
        'Bayview': 27,
        'Haight-Ashbury': 16,
        'Russian Hill': 8,
        'The Castro': 22,
        'Richmond District': 11,
        'Union Square': 16,
        'Sunset District': 19,
    },
    'Richmond District': {
        'Financial District': 22,
        'Fisherman\'s Wharf': 18,
        'Presidio': 7,
        'Bayview': 27,
        'Haight-Ashbury': 10,
        'Russian Hill': 13,
        'The Castro': 16,
        'Marina District': 9,
        'Union Square': 21,
        'Sunset District': 11,
    },
    'Union Square': {
        'Financial District': 9,
        'Fisherman\'s Wharf': 15,
        'Presidio': 24,
        'Bayview': 15,
        'Haight-Ashbury': 18,
        'Russian Hill': 13,
        'The Castro': 17,
        'Marina District': 18,
        'Richmond District': 20,
        'Sunset District': 27,
    },
    'Sunset District': {
        'Financial District': 30,
        'Fisherman\'s Wharf': 29,
        'Presidio': 16,
        'Bayview': 22,
        'Haight-Ashbury': 15,
        'Russian Hill': 24,
        'The Castro': 17,
        'Marina District': 21,
        'Richmond District': 12,
        'Union Square': 30,
    }
}

# Friends' data
friends = [
    {
        'name': 'Mark',
        'location': 'Fisherman\'s Wharf',
        'start': '8:15',
        'end': '10:00',
        'duration': 30,
    },
    {
        'name': 'Stephanie',
        'location': 'Presidio',
        'start': '12:15',
        'end': '15:00',
        'duration': 75,
    },
    {
        'name': 'Betty',
        'location': 'Bayview',
        'start': '7:15',
        'end': '20:30',
        'duration': 15,
    },
    {
        'name': 'Lisa',
        'location': 'Haight-Ashbury',
        'start': '15:30',
        'end': '18:30',
        'duration': 45,
    },
    {
        'name': 'William',
        'location': 'Russian Hill',
        'start': '18:45',
        'end': '20:00',
        'duration': 60,
    },
    {
        'name': 'Brian',
        'location': 'The Castro',
        'start': '9:15',
        'end': '13:15',
        'duration': 30,
    },
    {
        'name': 'Joseph',
        'location': 'Marina District',
        'start': '10:45',
        'end': '15:00',
        'duration': 90,
    },
    {
        'name': 'Ashley',
        'location': 'Richmond District',
        'start': '9:45',
        'end': '11:15',
        'duration': 45,
    },
    {
        'name': 'Patricia',
        'location': 'Union Square',
        'start': '16:30',
        'end': '20:00',
        'duration': 120,
    },
    {
        'name': 'Karen',
        'location': 'Sunset District',
        'start': '16:30',
        'end': '22:00',
        'duration': 105,
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
    current_location = 'Financial District'
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