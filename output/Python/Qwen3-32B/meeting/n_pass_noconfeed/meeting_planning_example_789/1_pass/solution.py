import itertools
import json

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define travel times between locations
travel_times = {
    'Union Square': {
        'Russian Hill': 13,
        'Alamo Square': 15,
        'Haight-Ashbury': 18,
        'Marina District': 18,
        'Bayview': 15,
        'Chinatown': 7,
        'Presidio': 24,
        'Sunset District': 27
    },
    'Russian Hill': {
        'Union Square': 10,
        'Alamo Square': 15,
        'Haight-Ashbury': 17,
        'Marina District': 7,
        'Bayview': 23,
        'Chinatown': 9,
        'Presidio': 14,
        'Sunset District': 23
    },
    'Alamo Square': {
        'Union Square': 14,
        'Russian Hill': 13,
        'Haight-Ashbury': 5,
        'Marina District': 15,
        'Bayview': 16,
        'Chinatown': 15,
        'Presidio': 17,
        'Sunset District': 16
    },
    'Haight-Ashbury': {
        'Union Square': 19,
        'Russian Hill': 17,
        'Alamo Square': 5,
        'Marina District': 17,
        'Bayview': 18,
        'Chinatown': 19,
        'Presidio': 15,
        'Sunset District': 15
    },
    'Marina District': {
        'Union Square': 16,
        'Russian Hill': 8,
        'Alamo Square': 15,
        'Haight-Ashbury': 16,
        'Bayview': 27,
        'Chinatown': 15,
        'Presidio': 10,
        'Sunset District': 19
    },
    'Bayview': {
        'Union Square': 18,
        'Russian Hill': 23,
        'Alamo Square': 16,
        'Haight-Ashbury': 19,
        'Marina District': 27,
        'Chinatown': 19,
        'Presidio': 32,
        'Sunset District': 23
    },
    'Chinatown': {
        'Union Square': 7,
        'Russian Hill': 7,
        'Alamo Square': 17,
        'Haight-Ashbury': 19,
        'Marina District': 12,
        'Bayview': 20,
        'Presidio': 19,
        'Sunset District': 29
    },
    'Presidio': {
        'Union Square': 22,
        'Russian Hill': 14,
        'Alamo Square': 19,
        'Haight-Ashbury': 15,
        'Marina District': 11,
        'Bayview': 31,
        'Chinatown': 21,
        'Sunset District': 15
    },
    'Sunset District': {
        'Union Square': 30,
        'Russian Hill': 24,
        'Alamo Square': 17,
        'Haight-Ashbury': 15,
        'Marina District': 21,
        'Bayview': 22,
        'Chinatown': 30,
        'Presidio': 16
    }
}

# Define friends' constraints
friends_list = [
    {
        'name': 'Betty',
        'location': 'Russian Hill',
        'available_start': 7 * 60 + 0,  # 420
        'available_end': 16 * 60 + 45,  # 1005
        'required_duration': 105
    },
    {
        'name': 'Melissa',
        'location': 'Alamo Square',
        'available_start': 9 * 60 + 30,  # 570
        'available_end': 17 * 60 + 15,  # 1035
        'required_duration': 105
    },
    {
        'name': 'Joshua',
        'location': 'Haight-Ashbury',
        'available_start': 12 * 60 + 15, # 735
        'available_end': 19 * 60 + 0,   # 1140
        'required_duration': 90
    },
    {
        'name': 'Jeffrey',
        'location': 'Marina District',
        'available_start': 12 * 60 + 15, # 735
        'available_end': 18 * 60 + 0,   # 1080
        'required_duration': 45
    },
    {
        'name': 'James',
        'location': 'Bayview',
        'available_start': 7 * 60 + 30, # 450
        'available_end': 20 * 60 + 0,   # 1200
        'required_duration': 90
    },
    {
        'name': 'Anthony',
        'location': 'Chinatown',
        'available_start': 11 * 60 + 45, # 705
        'available_end': 13 * 60 + 30,   # 810
        'required_duration': 75
    },
    {
        'name': 'Timothy',
        'location': 'Presidio',
        'available_start': 12 * 60 + 30, # 750
        'available_end': 14 * 60 + 45,   # 885
        'required_duration': 90
    },
    {
        'name': 'Emily',
        'location': 'Sunset District',
        'available_start': 19 * 60 + 30, # 1170
        'available_end': 21 * 60 + 30,   # 1290
        'required_duration': 120
    }
]

def is_feasible(perm):
    current_time = 540  # 9:00 AM
    current_location = 'Union Square'
    for friend in perm:
        # Get travel time from current location to friend's location
        dest = friend['location']
        if current_location not in travel_times or dest not in travel_times[current_location]:
            return False
        travel_time = travel_times[current_location][dest]
        arrival_time = current_time + travel_time
        # Check if arrival_time is before or after friend's available start
        available_start = friend['available_start']
        available_end = friend['available_end']
        required_duration = friend['required_duration']
        # The earliest we can start is max(arrival_time, available_start)
        start_time = max(arrival_time, available_start)
        # The latest we can start is available_end - required_duration
        latest_start = available_end - required_duration
        if start_time > latest_start:
            return False
        # Schedule the meeting
        end_time = start_time + required_duration
        current_time = end_time
        current_location = dest
    return True

max_meetings = 0
best_perm = []

for r in range(1, len(friends_list) + 1):
    for perm in itertools.permutations(friends_list, r):
        if is_feasible(perm):
            if len(perm) > max_meetings:
                max_meetings = len(perm)
                best_perm = perm

# Generate the itinerary
itinerary = []
current_time = 540
current_location = 'Union Square'

for friend in best_perm:
    dest = friend['location']
    travel_time = travel_times[current_location][dest]
    arrival_time = current_time + travel_time
    available_start = friend['available_start']
    available_end = friend['available_end']
    required_duration = friend['required_duration']
    start_time = max(arrival_time, available_start)
    end_time = start_time + required_duration
    itinerary.append({
        'action': 'meet',
        'location': dest,
        'person': friend['name'],
        'start_time': minutes_to_time_str(start_time),
        'end_time': minutes_to_time_str(end_time)
    })
    current_time = end_time
    current_location = dest

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))