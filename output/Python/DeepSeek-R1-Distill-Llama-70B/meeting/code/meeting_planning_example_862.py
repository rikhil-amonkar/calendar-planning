import itertools
import json

# Travel times in minutes between locations
travel_times = {
    'Mission District': {
        'Alamo Square': 11,
        'Presidio': 25,
        'Russian Hill': 15,
        'North Beach': 17,
        'Golden Gate Park': 17,
        'Richmond District': 20,
        'Embarcadero': 19,
        'Financial District': 15,
        'Marina District': 19,
    },
    'Alamo Square': {
        'Mission District': 10,
        'Presidio': 17,
        'Russian Hill': 13,
        'North Beach': 15,
        'Golden Gate Park': 9,
        'Richmond District': 11,
        'Embarcadero': 16,
        'Financial District': 17,
        'Marina District': 15,
    },
    'Presidio': {
        'Mission District': 26,
        'Alamo Square': 19,
        'Russian Hill': 14,
        'North Beach': 18,
        'Golden Gate Park': 12,
        'Richmond District': 7,
        'Embarcadero': 20,
        'Financial District': 23,
        'Marina District': 11,
    },
    'Russian Hill': {
        'Mission District': 16,
        'Alamo Square': 15,
        'Presidio': 14,
        'North Beach': 5,
        'Golden Gate Park': 21,
        'Richmond District': 14,
        'Embarcadero': 8,
        'Financial District': 11,
        'Marina District': 7,
    },
    'North Beach': {
        'Mission District': 18,
        'Alamo Square': 16,
        'Presidio': 17,
        'Russian Hill': 4,
        'Golden Gate Park': 22,
        'Richmond District': 18,
        'Embarcadero': 6,
        'Financial District': 8,
        'Marina District': 9,
    },
    'Golden Gate Park': {
        'Mission District': 17,
        'Alamo Square': 9,
        'Presidio': 11,
        'Russian Hill': 19,
        'North Beach': 23,
        'Richmond District': 7,
        'Embarcadero': 25,
        'Financial District': 26,
        'Marina District': 16,
    },
    'Richmond District': {
        'Mission District': 20,
        'Alamo Square': 13,
        'Presidio': 7,
        'Russian Hill': 13,
        'North Beach': 17,
        'Golden Gate Park': 9,
        'Embarcadero': 19,
        'Financial District': 22,
        'Marina District': 9,
    },
    'Embarcadero': {
        'Mission District': 20,
        'Alamo Square': 19,
        'Presidio': 20,
        'Russian Hill': 8,
        'North Beach': 5,
        'Golden Gate Park': 25,
        'Richmond District': 21,
        'Financial District': 5,
        'Marina District': 12,
    },
    'Financial District': {
        'Mission District': 17,
        'Alamo Square': 17,
        'Presidio': 22,
        'Russian Hill': 11,
        'North Beach': 7,
        'Golden Gate Park': 23,
        'Richmond District': 21,
        'Embarcadero': 4,
        'Marina District': 15,
    },
    'Marina District': {
        'Mission District': 20,
        'Alamo Square': 15,
        'Presidio': 10,
        'Russian Hill': 8,
        'North Beach': 11,
        'Golden Gate Park': 18,
        'Richmond District': 11,
        'Embarcadero': 14,
        'Financial District': 17,
    }
}

# Friends' data
friends = [
    {
        'name': 'Laura',
        'location': 'Alamo Square',
        'start': '14:30',
        'end': '16:15',
        'duration': 75,
    },
    {
        'name': 'Brian',
        'location': 'Presidio',
        'start': '10:15',
        'end': '17:00',
        'duration': 30,
    },
    {
        'name': 'Karen',
        'location': 'Russian Hill',
        'start': '18:00',
        'end': '20:15',
        'duration': 90,
    },
    {
        'name': 'Stephanie',
        'location': 'North Beach',
        'start': '10:15',
        'end': '16:00',
        'duration': 75,
    },
    {
        'name': 'Helen',
        'location': 'Golden Gate Park',
        'start': '11:30',
        'end': '21:45',
        'duration': 120,
    },
    {
        'name': 'Sandra',
        'location': 'Richmond District',
        'start': '8:00',
        'end': '15:15',
        'duration': 30,
    },
    {
        'name': 'Mary',
        'location': 'Embarcadero',
        'start': '16:45',
        'end': '18:45',
        'duration': 120,
    },
    {
        'name': 'Deborah',
        'location': 'Financial District',
        'start': '19:00',
        'end': '20:45',
        'duration': 105,
    },
    {
        'name': 'Elizabeth',
        'location': 'Marina District',
        'start': '8:30',
        'end': '13:15',
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
    current_location = 'Mission District'
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