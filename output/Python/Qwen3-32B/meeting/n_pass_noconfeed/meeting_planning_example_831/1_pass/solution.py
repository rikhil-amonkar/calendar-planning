import itertools
import json

# Define travel times between locations
travel_times = {
    'Presidio': {
        'Fishermans Wharf': 19,
        'Alamo Square': 19,
        'Financial District': 23,
        'Union Square': 22,
        'Sunset District': 15,
        'Embarcadero': 20,
        'Golden Gate Park': 12,
        'Chinatown': 21,
        'Richmond District': 7,
    },
    'Fishermans Wharf': {
        'Presidio': 17,
        'Alamo Square': 21,
        'Financial District': 11,
        'Union Square': 13,
        'Sunset District': 27,
        'Embarcadero': 8,
        'Golden Gate Park': 25,
        'Chinatown': 12,
        'Richmond District': 18,
    },
    'Alamo Square': {
        'Presidio': 17,
        'Fishermans Wharf': 19,
        'Financial District': 17,
        'Union Square': 14,
        'Sunset District': 16,
        'Embarcadero': 16,
        'Golden Gate Park': 9,
        'Chinatown': 15,
        'Richmond District': 11,
    },
    'Financial District': {
        'Presidio': 22,
        'Fishermans Wharf': 10,
        'Alamo Square': 17,
        'Union Square': 9,
        'Sunset District': 30,
        'Embarcadero': 4,
        'Golden Gate Park': 23,
        'Chinatown': 5,
        'Richmond District': 21,
    },
    'Union Square': {
        'Presidio': 24,
        'Fishermans Wharf': 15,
        'Alamo Square': 15,
        'Financial District': 9,
        'Sunset District': 27,
        'Embarcadero': 11,
        'Golden Gate Park': 22,
        'Chinatown': 7,
        'Richmond District': 20,
    },
    'Sunset District': {
        'Presidio': 16,
        'Fishermans Wharf': 29,
        'Alamo Square': 17,
        'Financial District': 30,
        'Union Square': 30,
        'Embarcadero': 30,
        'Golden Gate Park': 11,
        'Chinatown': 30,
        'Richmond District': 12,
    },
    'Embarcadero': {
        'Presidio': 20,
        'Fishermans Wharf': 6,
        'Alamo Square': 19,
        'Financial District': 5,
        'Union Square': 10,
        'Sunset District': 30,
        'Golden Gate Park': 25,
        'Chinatown': 7,
        'Richmond District': 21,
    },
    'Golden Gate Park': {
        'Presidio': 11,
        'Fishermans Wharf': 24,
        'Alamo Square': 9,
        'Financial District': 26,
        'Union Square': 22,
        'Sunset District': 10,
        'Embarcadero': 25,
        'Chinatown': 23,
        'Richmond District': 7,
    },
    'Chinatown': {
        'Presidio': 19,
        'Fishermans Wharf': 8,
        'Alamo Square': 17,
        'Financial District': 5,
        'Union Square': 7,
        'Sunset District': 29,
        'Embarcadero': 5,
        'Golden Gate Park': 23,
        'Richmond District': 20,
    },
    'Richmond District': {
        'Presidio': 7,
        'Fishermans Wharf': 18,
        'Alamo Square': 13,
        'Financial District': 22,
        'Union Square': 21,
        'Sunset District': 11,
        'Embarcadero': 19,
        'Golden Gate Park': 9,
        'Chinatown': 20,
    },
}

friends = [
    {
        'name': 'Jeffrey',
        'location': 'Fishermans Wharf',
        'start_time': 10 * 60 + 15,  # 615
        'end_time': 13 * 60,          # 780
        'duration': 90
    },
    {
        'name': 'Ronald',
        'location': 'Alamo Square',
        'start_time': 7 * 60 + 45,    # 465
        'end_time': 14 * 60 + 45,     # 885
        'duration': 120
    },
    {
        'name': 'Jason',
        'location': 'Financial District',
        'start_time': 10 * 60 + 45,   # 645
        'end_time': 16 * 60,          # 960
        'duration': 105
    },
    {
        'name': 'Melissa',
        'location': 'Union Square',
        'start_time': 17 * 60 + 45,   # 1065
        'end_time': 18 * 60 + 15,     # 1095
        'duration': 15
    },
    {
        'name': 'Elizabeth',
        'location': 'Sunset District',
        'start_time': 14 * 60 + 45,   # 885
        'end_time': 17 * 60 + 30,     # 1050
        'duration': 105
    },
    {
        'name': 'Margaret',
        'location': 'Embarcadero',
        'start_time': 13 * 60 + 15,   # 795
        'end_time': 19 * 60,          # 1140
        'duration': 90
    },
    {
        'name': 'George',
        'location': 'Golden Gate Park',
        'start_time': 19 * 60,        # 1140
        'end_time': 22 * 60,          # 1320
        'duration': 75
    },
    {
        'name': 'Richard',
        'location': 'Chinatown',
        'start_time': 9 * 60 + 30,    # 570
        'end_time': 21 * 60,          # 1260
        'duration': 15
    },
    {
        'name': 'Laura',
        'location': 'Richmond District',
        'start_time': 9 * 60 + 45,    # 585
        'end_time': 18 * 60,          # 1080
        'duration': 60
    }
]

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

best_itinerary = []
max_met = 0

# Generate all permutations of friends
for perm in itertools.permutations(friends):
    current_time = 9 * 60  # 9:00 AM in minutes
    current_location = 'Presidio'
    itinerary = []
    for friend in perm:
        # Calculate travel time
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        # Determine earliest start time
        start_time = max(arrival_time, friend['start_time'])
        end_time = start_time + friend['duration']
        # Check if end time exceeds friend's end time
        if end_time > friend['end_time']:
            break
        # Add to itinerary
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': start_time,
            'end_time': end_time
        })
        # Update current time and location
        current_time = end_time
        current_location = friend['location']
    # Check if this itinerary is better
    if len(itinerary) > max_met:
        max_met = len(itinerary)
        best_itinerary = itinerary
    # Early exit if we found a perfect itinerary (all friends met)
    if len(itinerary) == len(friends):
        break  # No need to check other permutations

# Convert the best itinerary to the required format
result = {
    "itinerary": [
        {
            "action": "meet",
            "location": entry['location'],
            "person": entry['person'],
            "start_time": minutes_to_time_str(entry['start_time']),
            "end_time": minutes_to_time_str(entry['end_time'])
        }
        for entry in best_itinerary
    ]
}

print(json.dumps(result, indent=2))