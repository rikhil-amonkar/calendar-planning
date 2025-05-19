import itertools
import json

# Travel times in minutes between locations
travel_times = {
    'Presidio': {
        'Haight-Ashbury': 15,
        'Nob Hill': 18,
        'Russian Hill': 14,
        'North Beach': 18,
        'Chinatown': 21,
        'Union Square': 22,
        'Embarcadero': 20,
        'Financial District': 23,
        'Marina District': 11,
    },
    'Haight-Ashbury': {
        'Presidio': 15,
        'Nob Hill': 15,
        'Russian Hill': 17,
        'North Beach': 19,
        'Chinatown': 19,
        'Union Square': 19,
        'Embarcadero': 20,
        'Financial District': 21,
        'Marina District': 17,
    },
    'Nob Hill': {
        'Presidio': 17,
        'Haight-Ashbury': 13,
        'Russian Hill': 5,
        'North Beach': 8,
        'Chinatown': 6,
        'Union Square': 7,
        'Embarcadero': 9,
        'Financial District': 9,
        'Marina District': 11,
    },
    'Russian Hill': {
        'Presidio': 14,
        'Haight-Ashbury': 17,
        'Nob Hill': 5,
        'North Beach': 5,
        'Chinatown': 9,
        'Union Square': 10,
        'Embarcadero': 8,
        'Financial District': 11,
        'Marina District': 7,
    },
    'North Beach': {
        'Presidio': 17,
        'Haight-Ashbury': 18,
        'Nob Hill': 7,
        'Russian Hill': 4,
        'Chinatown': 6,
        'Union Square': 7,
        'Embarcadero': 6,
        'Financial District': 8,
        'Marina District': 9,
    },
    'Chinatown': {
        'Presidio': 19,
        'Haight-Ashbury': 19,
        'Nob Hill': 9,
        'Russian Hill': 7,
        'North Beach': 3,
        'Union Square': 7,
        'Embarcadero': 5,
        'Financial District': 5,
        'Marina District': 12,
    },
    'Union Square': {
        'Presidio': 24,
        'Haight-Ashbury': 18,
        'Nob Hill': 9,
        'Russian Hill': 13,
        'North Beach': 10,
        'Chinatown': 7,
        'Embarcadero': 11,
        'Financial District': 9,
        'Marina District': 18,
    },
    'Embarcadero': {
        'Presidio': 20,
        'Haight-Ashbury': 21,
        'Nob Hill': 10,
        'Russian Hill': 8,
        'North Beach': 5,
        'Chinatown': 7,
        'Union Square': 10,
        'Financial District': 5,
        'Marina District': 12,
    },
    'Financial District': {
        'Presidio': 22,
        'Haight-Ashbury': 19,
        'Nob Hill': 8,
        'Russian Hill': 11,
        'North Beach': 7,
        'Chinatown': 5,
        'Union Square': 9,
        'Embarcadero': 4,
        'Marina District': 15,
    },
    'Marina District': {
        'Presidio': 10,
        'Haight-Ashbury': 16,
        'Nob Hill': 12,
        'Russian Hill': 8,
        'North Beach': 11,
        'Chinatown': 15,
        'Union Square': 16,
        'Embarcadero': 14,
        'Financial District': 17,
    }
}

# Friends' data
friends = [
    {
        'name': 'Karen',
        'location': 'Haight-Ashbury',
        'start': '21:00',
        'end': '21:45',
        'duration': 45,
    },
    {
        'name': 'Jessica',
        'location': 'Nob Hill',
        'start': '13:45',
        'end': '21:00',
        'duration': 90,
    },
    {
        'name': 'Brian',
        'location': 'Russian Hill',
        'start': '15:30',
        'end': '21:45',
        'duration': 60,
    },
    {
        'name': 'Kenneth',
        'location': 'North Beach',
        'start': '9:45',
        'end': '21:00',
        'duration': 30,
    },
    {
        'name': 'Jason',
        'location': 'Chinatown',
        'start': '8:15',
        'end': '11:45',
        'duration': 75,
    },
    {
        'name': 'Stephanie',
        'location': 'Union Square',
        'start': '14:45',
        'end': '18:45',
        'duration': 105,
    },
    {
        'name': 'Kimberly',
        'location': 'Embarcadero',
        'start': '9:45',
        'end': '19:30',
        'duration': 75,
    },
    {
        'name': 'Steven',
        'location': 'Financial District',
        'start': '7:15',
        'end': '21:15',
        'duration': 60,
    },
    {
        'name': 'Mark',
        'location': 'Marina District',
        'start': '10:15',
        'end': '13:00',
        'duration': 75,
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
    current_location = 'Presidio'
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