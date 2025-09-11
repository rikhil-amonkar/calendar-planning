import itertools
import json

def time_to_minutes(t_str):
    h, m = map(int, t_str.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    minute = m % 60
    return f"{h}:{minute:02d}"

# Define friends with their data
friends = [
    {
        'name': 'William',
        'location': 'Embarcadero',
        'available_start': 7 * 60 + 0,  # 7:00 AM
        'available_end': 9 * 60 + 0,    # 9:00 AM
        'required_duration': 90
    },
    {
        'name': 'Stephanie',
        'location': 'Nob Hill',
        'available_start': 7 * 60 + 30,  # 7:30 AM
        'available_end': 9 * 60 + 30,    # 9:30 AM
        'required_duration': 45
    },
    {
        'name': 'Joseph',
        'location': 'Alamo Square',
        'available_start': 11 * 60 + 30,  # 11:30 AM
        'available_end': 12 * 60 + 45,    # 12:45 PM
        'required_duration': 15
    },
    {
        'name': 'Karen',
        'location': 'Russian Hill',
        'available_start': 14 * 60 + 30,  # 2:30 PM
        'available_end': 19 * 60 + 45,    # 7:45 PM
        'required_duration': 30
    },
    {
        'name': 'Kimberly',
        'location': 'North Beach',
        'available_start': 15 * 60 + 45,  # 3:45 PM
        'available_end': 19 * 60 + 15,    # 7:15 PM
        'required_duration': 30
    },
    {
        'name': 'Laura',
        'location': 'The Castro',
        'available_start': 19 * 60 + 45,  # 7:45 PM
        'available_end': 21 * 60 + 30,    # 9:30 PM
        'required_duration': 105
    },
    {
        'name': 'Daniel',
        'location': 'Golden Gate Park',
        'available_start': 21 * 60 + 15,  # 9:15 PM
        'available_end': 21 * 60 + 45,    # 9:45 PM
        'required_duration': 15
    }
]

# Define travel times between locations
travel_times = {
    "Fisherman's Wharf": {
        "The Castro": 26,
        "Golden Gate Park": 25,
        "Embarcadero": 8,
        "Russian Hill": 7,
        "Nob Hill": 11,
        "Alamo Square": 20,
        "North Beach": 6
    },
    "The Castro": {
        "Fisherman's Wharf": 24,
        "Golden Gate Park": 11,
        "Embarcadero": 22,
        "Russian Hill": 18,
        "Nob Hill": 16,
        "Alamo Square": 8,
        "North Beach": 20
    },
    "Golden Gate Park": {
        "Fisherman's Wharf": 24,
        "The Castro": 13,
        "Embarcadero": 25,
        "Russian Hill": 19,
        "Nob Hill": 20,
        "Alamo Square": 10,
        "North Beach": 24
    },
    "Embarcadero": {
        "Fisherman's Wharf": 6,
        "The Castro": 25,
        "Golden Gate Park": 25,
        "Russian Hill": 8,
        "Nob Hill": 10,
        "Alamo Square": 19,
        "North Beach": 5
    },
    "Russian Hill": {
        "Fisherman's Wharf": 7,
        "The Castro": 21,
        "Golden Gate Park": 21,
        "Embarcadero": 8,
        "Nob Hill": 5,
        "Alamo Square": 15,
        "North Beach": 5
    },
    "Nob Hill": {
        "Fisherman's Wharf": 11,
        "The Castro": 17,
        "Golden Gate Park": 17,
        "Embarcadero": 9,
        "Russian Hill": 5,
        "Alamo Square": 11,
        "North Beach": 8
    },
    "Alamo Square": {
        "Fisherman's Wharf": 19,
        "The Castro": 8,
        "Golden Gate Park": 9,
        "Embarcadero": 17,
        "Russian Hill": 13,
        "Nob Hill": 11,
        "North Beach": 15
    },
    "North Beach": {
        "Fisherman's Wharf": 5,
        "The Castro": 22,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Russian Hill": 4,
        "Nob Hill": 7,
        "Alamo Square": 16
    }
}

best_itinerary = []
max_met = 0

# Starting time and location
start_time = 9 * 60  # 9:00 AM in minutes
start_location = "Fisherman's Wharf"

for perm in itertools.permutations(friends):
    current_time = start_time
    current_location = start_location
    itinerary = []
    met_count = 0

    for friend in perm:
        # Calculate arrival time at friend's location
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time

        # Determine earliest possible meeting start time
        friend_start = friend['available_start']
        friend_end = friend['available_end']
        duration = friend['required_duration']

        start_meeting = max(arrival_time, friend_start)
        end_meeting = start_meeting + duration

        # Check if meeting is possible
        if end_meeting > friend_end:
            break  # Can't meet this friend, break the loop for this permutation

        # Add to itinerary
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(start_meeting),
            'end_time': minutes_to_time(end_meeting)
        })
        met_count += 1
        current_time = end_meeting
        current_location = friend['location']

    # Update best itinerary if this one is better
    if met_count > max_met:
        max_met = met_count
        best_itinerary = itinerary
    elif met_count == max_met and met_count > 0:
        # In case of tie, keep the first one encountered
        pass

# Output the best itinerary as JSON
result = {
    "itinerary": best_itinerary
}

print(json.dumps(result, indent=2))