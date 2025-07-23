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
    'Sunset District': {
        'Russian Hill': 24,
        'The Castro': 17,
        'Richmond District': 12,
        'Marina District': 21,
        'North Beach': 29,
        'Union Square': 30,
        'Golden Gate Park': 11
    },
    'Russian Hill': {
        'Sunset District': 23,
        'The Castro': 21,
        'Richmond District': 14,
        'Marina District': 7,
        'North Beach': 5,
        'Union Square': 11,
        'Golden Gate Park': 21
    },
    'The Castro': {
        'Sunset District': 17,
        'Russian Hill': 18,
        'Richmond District': 16,
        'Marina District': 21,
        'North Beach': 20,
        'Union Square': 19,
        'Golden Gate Park': 11
    },
    'Richmond District': {
        'Sunset District': 11,
        'Russian Hill': 13,
        'The Castro': 16,
        'Marina District': 9,
        'North Beach': 17,
        'Union Square': 21,
        'Golden Gate Park': 9
    },
    'Marina District': {
        'Sunset District': 19,
        'Russian Hill': 8,
        'The Castro': 22,
        'Richmond District': 11,
        'North Beach': 11,
        'Union Square': 16,
        'Golden Gate Park': 18
    },
    'Marina District': {
        'Sunset District': 19,
        'Russian Hill': 8,
        'The Castro': 22,
        'Richmond District': 11,
        'North Beach': 11,
        'Union Square': 16,
        'Golden Gate Park': 18
    },
    'North Beach': {
        'Sunset District': 27,
        'Russian Hill': 4,
        'The Castro': 22,
        'Richmond District': 18,
        'Marina District': 9,
        'Union Square': 7,
        'Golden Gate Park': 22
    },
    'Union Square': {
        'Sunset District': 26,
        'Russian Hill': 13,
        'The Castro': 19,
        'Richmond District': 20,
        'Marina District': 18,
        'North Beach': 10,
        'Golden Gate Park': 22
    },
    'Golden Gate Park': {
        'Sunset District': 10,
        'Russian Hill': 19,
        'The Castro': 13,
        'Richmond District': 7,
        'Marina District': 16,
        'North Beach': 24,
        'Union Square': 22
    }
}

friends = [
    {
        'name': 'Karen',
        'location': 'Russian Hill',
        'available_start': '20:45',
        'available_end': '21:45',
        'duration': 60
    },
    {
        'name': 'Jessica',
        'location': 'The Castro',
        'available_start': '15:45',
        'available_end': '19:30',
        'duration': 60
    },
    {
        'name': 'Matthew',
        'location': 'Richmond District',
        'available_start': '7:30',
        'available_end': '15:15',
        'duration': 15
    },
    {
        'name': 'Michelle',
        'location': 'Marina District',
        'available_start': '10:30',
        'available_end': '18:45',
        'duration': 75
    },
    {
        'name': 'Carol',
        'location': 'North Beach',
        'available_start': '12:00',
        'available_end': '17:00',
        'duration': 90
    },
    {
        'name': 'Stephanie',
        'location': 'Union Square',
        'available_start': '10:45',
        'available_end': '14:15',
        'duration': 30
    },
    {
        'name': 'Linda',
        'location': 'Golden Gate Park',
        'available_start': '10:45',
        'available_end': '22:00',
        'duration': 90
    }
]

# Filter friends who can be met (available time >= duration)
valid_friends = [f for f in friends if (time_to_minutes(f['available_end']) - time_to_minutes(f['available_start']) >= f['duration']]

# Generate all possible orders of meeting friends
best_itinerary = []
max_meetings = 0

# Since checking all permutations is computationally expensive for large n, we'll limit to 5 friends
# We'll prioritize friends with earlier available times and shorter durations
valid_friends_sorted = sorted(valid_friends, key=lambda x: (time_to_minutes(x['available_start']), x['duration']))
selected_friends = valid_friends_sorted[:5]

for order in permutations(selected_friends):
    current_location = 'Sunset District'
    current_time = time_to_minutes('9:00')
    itinerary = []
    meetings = 0
    
    for friend in order:
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        
        available_start = time_to_minutes(friend['available_start'])
        available_end = time_to_minutes(friend['available_end'])
        
        # Calculate meeting window
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + friend['duration']
        
        if meeting_end <= available_end:
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(meeting_start),
                'end_time': minutes_to_time(meeting_end)
            })
            current_location = friend['location']
            current_time = meeting_end
            meetings += 1
        else:
            # Can't meet this friend in this order
            break
    
    if meetings > max_meetings:
        max_meetings = meetings
        best_itinerary = itinerary
    elif meetings == max_meetings and meetings > 0:
        # Prefer itinerary that ends earlier
        if current_time < time_to_minutes(best_itinerary[-1]['end_time']) if best_itinerary else True:
            best_itinerary = itinerary

# Output the best itinerary found
output = {
    "itinerary": best_itinerary
}

print(json.dumps(output, indent=2))