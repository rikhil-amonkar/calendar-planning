import itertools
import json

def time_str_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

# Define friends with their availability and meeting duration requirements
friends = [
    {
        'name': 'Mark',
        'location': 'Marina District',
        'available_start': '18:45',
        'available_end': '21:00',
        'min_duration': 90
    },
    {
        'name': 'Karen',
        'location': 'Financial District',
        'available_start': '9:30',
        'available_end': '12:45',
        'min_duration': 90
    },
    {
        'name': 'Barbara',
        'location': 'Alamo Square',
        'available_start': '10:00',
        'available_end': '19:30',
        'min_duration': 90
    },
    {
        'name': 'Nancy',
        'location': 'Golden Gate Park',
        'available_start': '16:45',
        'available_end': '20:00',
        'min_duration': 105
    },
    {
        'name': 'David',
        'location': 'The Castro',
        'available_start': '9:00',
        'available_end': '18:00',
        'min_duration': 120
    },
    {
        'name': 'Linda',
        'location': 'Bayview',
        'available_start': '18:15',
        'available_end': '19:45',
        'min_duration': 45
    },
    {
        'name': 'Kevin',
        'location': 'Sunset District',
        'available_start': '10:00',
        'available_end': '17:45',
        'min_duration': 120
    },
    {
        'name': 'Matthew',
        'location': 'Haight-Ashbury',
        'available_start': '10:15',
        'available_end': '15:30',
        'min_duration': 45
    },
    {
        'name': 'Andrew',
        'location': 'Nob Hill',
        'available_start': '11:45',
        'available_end': '16:45',
        'min_duration': 105
    },
]

# Convert time strings to minutes since midnight
for f in friends:
    f['available_start_minutes'] = time_str_to_minutes(f['available_start'])
    f['available_end_minutes'] = time_str_to_minutes(f['available_end'])

# Define travel times between locations
travel_times = {
    'Russian Hill': {
        'Marina District': 7,
        'Financial District': 11,
        'Alamo Square': 15,
        'Golden Gate Park': 21,
        'The Castro': 21,
        'Bayview': 23,
        'Sunset District': 23,
        'Haight-Ashbury': 17,
        'Nob Hill': 5,
    },
    'Marina District': {
        'Russian Hill': 8,
        'Financial District': 17,
        'Alamo Square': 15,
        'Golden Gate Park': 18,
        'The Castro': 22,
        'Bayview': 27,
        'Sunset District': 19,
        'Haight-Ashbury': 16,
        'Nob Hill': 12,
    },
    'Financial District': {
        'Russian Hill': 11,
        'Marina District': 15,
        'Alamo Square': 17,
        'Golden Gate Park': 23,
        'The Castro': 20,
        'Bayview': 19,
        'Sunset District': 30,
        'Haight-Ashbury': 19,
        'Nob Hill': 8,
    },
    'Alamo Square': {
        'Russian Hill': 13,
        'Marina District': 15,
        'Financial District': 17,
        'Golden Gate Park': 9,
        'The Castro': 8,
        'Bayview': 16,
        'Sunset District': 16,
        'Haight-Ashbury': 5,
        'Nob Hill': 11,
    },
    'Golden Gate Park': {
        'Russian Hill': 19,
        'Marina District': 16,
        'Financial District': 26,
        'Alamo Square': 9,
        'The Castro': 13,
        'Bayview': 23,
        'Sunset District': 10,
        'Haight-Ashbury': 7,
        'Nob Hill': 20,
    },
    'The Castro': {
        'Russian Hill': 18,
        'Marina District': 21,
        'Financial District': 21,
        'Alamo Square': 8,
        'Golden Gate Park': 11,
        'Bayview': 19,
        'Sunset District': 17,
        'Haight-Ashbury': 6,
        'Nob Hill': 16,
    },
    'Bayview': {
        'Russian Hill': 23,
        'Marina District': 27,
        'Financial District': 19,
        'Alamo Square': 16,
        'Golden Gate Park': 22,
        'The Castro': 19,
        'Sunset District': 23,
        'Haight-Ashbury': 19,
        'Nob Hill': 20,
    },
    'Sunset District': {
        'Russian Hill': 24,
        'Marina District': 21,
        'Financial District': 30,
        'Alamo Square': 17,
        'Golden Gate Park': 11,
        'The Castro': 17,
        'Bayview': 22,
        'Haight-Ashbury': 15,
        'Nob Hill': 27,
    },
    'Haight-Ashbury': {
        'Russian Hill': 17,
        'Marina District': 17,
        'Financial District': 21,
        'Alamo Square': 5,
        'Golden Gate Park': 7,
        'The Castro': 6,
        'Bayview': 18,
        'Sunset District': 15,
        'Nob Hill': 15,
    },
    'Nob Hill': {
        'Russian Hill': 5,
        'Marina District': 11,
        'Financial District': 9,
        'Alamo Square': 11,
        'Golden Gate Park': 17,
        'The Castro': 17,
        'Bayview': 19,
        'Sunset District': 24,
        'Haight-Ashbury': 13,
    },
}

def simulate_permutation(perm):
    current_time = 9 * 60  # Start at 9:00 AM in minutes
    current_location = 'Russian Hill'
    itinerary = []
    for friend in perm:
        # Calculate travel time
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        
        # Check if friend can be met
        friend_start = friend['available_start_minutes']
        friend_end = friend['available_end_minutes']
        min_duration = friend['min_duration']
        latest_start = friend_end - min_duration
        earliest_start = max(arrival_time, friend_start)
        
        if earliest_start > latest_start:
            return None  # Cannot meet this friend in this permutation
        
        # Schedule the meeting
        meeting_start = earliest_start
        meeting_end = meeting_start + min_duration
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': meeting_start,
            'end_time': meeting_end
        })
        
        # Update current time and location
        current_time = meeting_end
        current_location = friend['location']
    
    return itinerary

def to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

best_itinerary = []
max_length = 0

# Try all permutations of friends
for r in range(1, len(friends) + 1):
    for perm in itertools.permutations(friends, r):
        itinerary = simulate_permutation(perm)
        if itinerary is not None:
            if len(itinerary) > max_length:
                max_length = len(itinerary)
                best_itinerary = itinerary

# Convert times to string format
for item in best_itinerary:
    item['start_time'] = to_time_str(item['start_time'])
    item['end_time'] = to_time_str(item['end_time'])

result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))