import json

def time_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def find_best(current_time, current_location, visited_indices, friends, travel_time):
    best_itinerary = []
    for i in range(len(friends)):
        if i in visited_indices:
            continue
        friend = friends[i]
        loc = friend['location']
        # Calculate travel time to friend's location
        travel_time_minutes = travel_time[current_location][loc]
        arrival_time = current_time + travel_time_minutes
        possible_start = max(arrival_time, friend['start_time'])
        possible_end = possible_start + friend['required']
        if possible_end > friend['end_time']:
            continue  # can't meet this friend
        # Create new visited list
        new_visited = visited_indices + [i]
        # Create meeting entry
        meeting = {
            'action': 'meet',
            'location': loc,
            'person': friend['name'],
            'start_time': time_to_str(possible_start),
            'end_time': time_to_str(possible_end)
        }
        # Recursively find the best itinerary from this new state
        next_itinerary = find_best(possible_end, loc, new_visited, friends, travel_time)
        candidate_itinerary = [meeting] + next_itinerary
        if len(candidate_itinerary) > len(best_itinerary):
            best_itinerary = candidate_itinerary
    return best_itinerary

# Define friends
friends = [
    {
        'name': 'Stephanie',
        'location': 'Presidio',
        'start_time': 7 * 60 + 30,  # 7:30 AM
        'end_time': 10 * 60 + 15,   # 10:15 AM
        'required': 60
    },
    {
        'name': 'Jessica',
        'location': 'Nob Hill',
        'start_time': 16 * 60 + 30,  # 4:30 PM
        'end_time': 18 * 60 + 45,   # 6:45 PM
        'required': 120
    },
    {
        'name': 'Mary',
        'location': 'Union Square',
        'start_time': 16 * 60 + 45,  # 4:45 PM
        'end_time': 21 * 60 + 30,   # 9:30 PM
        'required': 60
    },
    {
        'name': 'Charles',
        'location': 'The Castro',
        'start_time': 16 * 60 + 30,  # 4:30 PM
        'end_time': 22 * 60 + 0,   # 10:00 PM
        'required': 105
    },
    {
        'name': 'Nancy',
        'location': 'North Beach',
        'start_time': 14 * 60 + 45,  # 2:45 PM
        'end_time': 20 * 60 + 0,   # 8:00 PM
        'required': 15
    },
    {
        'name': 'Thomas',
        'location': 'Fisherman\'s Wharf',
        'start_time': 13 * 60 + 30,  # 1:30 PM
        'end_time': 19 * 60 + 0,   # 7:00 PM
        'required': 30
    },
    {
        'name': 'Brian',
        'location': 'Marina District',
        'start_time': 12 * 60 + 15,  # 12:15 PM
        'end_time': 18 * 60 + 0,   # 6:00 PM
        'required': 60
    },
    {
        'name': 'Matthew',
        'location': 'Bayview',
        'start_time': 19 * 60 + 15,  # 7:15 PM
        'end_time': 22 * 60 + 0,   # 10:00 PM
        'required': 120
    },
    {
        'name': 'Karen',
        'location': 'Chinatown',
        'start_time': 19 * 60 + 15,  # 7:15 PM
        'end_time': 21 * 60 + 15,   # 9:15 PM
        'required': 90
    },
    {
        'name': 'Sarah',
        'location': 'Alamo Square',
        'start_time': 20 * 60 + 0,  # 8:00 PM
        'end_time': 21 * 60 + 45,   # 9:45 PM
        'required': 105
    },
]

# Define travel_time
travel_time = {
    'Embarcadero': {
        'Bayview': 21,
        'Chinatown': 7,
        'Alamo Square': 19,
        'Nob Hill': 10,
        'Presidio': 20,
        'Union Square': 10,
        'The Castro': 25,
        'North Beach': 5,
        'Fisherman\'s Wharf': 6,
        'Marina District': 12,
    },
    'Bayview': {
        'Embarcadero': 19,
        'Chinatown': 19,
        'Alamo Square': 16,
        'Nob Hill': 20,
        'Presidio': 32,
        'Union Square': 18,
        'The Castro': 19,
        'North Beach': 22,
        'Fisherman\'s Wharf': 25,
        'Marina District': 27,
    },
    'Chinatown': {
        'Embarcadero': 5,
        'Bayview': 20,
        'Alamo Square': 17,
        'Nob Hill': 9,
        'Presidio': 19,
        'Union Square': 7,
        'The Castro': 22,
        'North Beach': 3,
        'Fisherman\'s Wharf': 8,
        'Marina District': 12,
    },
    'Alamo Square': {
        'Embarcadero': 16,
        'Bayview': 16,
        'Chinatown': 15,
        'Nob Hill': 11,
        'Presidio': 17,
        'Union Square': 14,
        'The Castro': 8,
        'North Beach': 15,
        'Fisherman\'s Wharf': 19,
        'Marina District': 15,
    },
    'Nob Hill': {
        'Embarcadero': 9,
        'Bayview': 19,
        'Chinatown': 6,
        'Alamo Square': 11,
        'Presidio': 17,
        'Union Square': 7,
        'The Castro': 17,
        'North Beach': 8,
        'Fisherman\'s Wharf': 10,
        'Marina District': 11,
    },
    'Presidio': {
        'Embarcadero': 20,
        'Bayview': 31,
        'Chinatown': 21,
        'Alamo Square': 19,
        'Nob Hill': 18,
        'Union Square': 22,
        'The Castro': 21,
        'North Beach': 18,
        'Fisherman\'s Wharf': 19,
        'Marina District': 11,
    },
    'Union Square': {
        'Embarcadero': 11,
        'Bayview': 15,
        'Chinatown': 7,
        'Alamo Square': 15,
        'Nob Hill': 9,
        'Presidio': 24,
        'The Castro': 17,
        'North Beach': 10,
        'Fisherman\'s Wharf': 15,
        'Marina District': 18,
    },
    'The Castro': {
        'Embarcadero': 22,
        'Bayview': 19,
        'Chinatown': 22,
        'Alamo Square': 8,
        'Nob Hill': 16,
        'Presidio': 20,
        'Union Square': 19,
        'North Beach': 20,
        'Fisherman\'s Wharf': 24,
        'Marina District': 21,
    },
    'North Beach': {
        'Embarcadero': 6,
        'Bayview': 25,
        'Chinatown': 6,
        'Alamo Square': 16,
        'Nob Hill': 7,
        'Presidio': 17,
        'Union Square': 7,
        'The Castro': 23,
        'Fisherman\'s Wharf': 5,
        'Marina District': 9,
    },
    'Fisherman\'s Wharf': {
        'Embarcadero': 8,
        'Bayview': 26,
        'Chinatown': 12,
        'Alamo Square': 21,
        'Nob Hill': 11,
        'Presidio': 17,
        'Union Square': 13,
        'The Castro': 27,
        'North Beach': 6,
        'Marina District': 9,
    },
    'Marina District': {
        'Embarcadero': 14,
        'Bayview': 27,
        'Chinatown': 15,
        'Alamo Square': 15,
        'Nob Hill': 12,
        'Presidio': 10,
        'Union Square': 16,
        'The Castro': 22,
        'North Beach': 11,
        'Fisherman\'s Wharf': 10,
    },
}

# Initial parameters
start_time_minutes = 9 * 60  # 9:00 AM
start_location = 'Embarcadero'

itinerary = find_best(start_time_minutes, start_location, [], friends, travel_time)

# Output as JSON
result = {
    "itinerary": itinerary
}

print(json.dumps(result, indent=2))