import itertools
import json

def convert_minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define travel times between districts
travel_times = {
    'Richmond District': {
        'Sunset District': 11,
        'Haight-Ashbury': 10,
        'Mission District': 20,
        'Golden Gate Park': 9,
    },
    'Sunset District': {
        'Richmond District': 12,
        'Haight-Ashbury': 15,
        'Mission District': 24,
        'Golden Gate Park': 11,
    },
    'Haight-Ashbury': {
        'Richmond District': 10,
        'Sunset District': 15,
        'Mission District': 11,
        'Golden Gate Park': 7,
    },
    'Mission District': {
        'Richmond District': 20,
        'Sunset District': 24,
        'Haight-Ashbury': 12,
        'Golden Gate Park': 17,
    },
    'Golden Gate Park': {
        'Richmond District': 7,
        'Sunset District': 10,
        'Haight-Ashbury': 7,
        'Mission District': 17,
    },
}

# Define friends with their constraints
friends = [
    {
        'name': 'Sarah',
        'location': 'Sunset District',
        'available_start': 10 * 60 + 45,  # 645 minutes (10:45 AM)
        'available_end': 19 * 60,         # 1140 minutes (7:00 PM)
        'min_duration': 30
    },
    {
        'name': 'Richard',
        'location': 'Haight-Ashbury',
        'available_start': 11 * 60 + 45,  # 705 minutes (11:45 AM)
        'available_end': 15 * 60 + 45,    # 945 minutes (3:45 PM)
        'min_duration': 90
    },
    {
        'name': 'Elizabeth',
        'location': 'Mission District',
        'available_start': 11 * 60,       # 660 minutes (11:00 AM)
        'available_end': 17 * 60 + 15,    # 1035 minutes (5:15 PM)
        'min_duration': 120
    },
    {
        'name': 'Michelle',
        'location': 'Golden Gate Park',
        'available_start': 18 * 60 + 15,  # 1095 minutes (6:15 PM)
        'available_end': 20 * 60 + 45,    # 1245 minutes (8:45 PM)
        'min_duration': 90
    }
]

best_itinerary = []
max_visited = 0

# Generate all permutations of friends and check each one
for perm in itertools.permutations(friends):
    current_time = 9 * 60  # Start at 9:00 AM (540 minutes)
    current_location = 'Richmond District'
    itinerary = []
    valid = True

    for friend in perm:
        # Calculate travel time to the friend's location
        destination = friend['location']
        travel_time = travel_times[current_location][destination]
        arrival_time_candidate = current_time + travel_time

        # Determine actual arrival time considering friend's availability
        arrival_time = max(arrival_time_candidate, friend['available_start'])

        # Check if meeting can fit within the friend's available time
        meeting_end_time = arrival_time + friend['min_duration']
        if meeting_end_time > friend['available_end']:
            valid = False
            break

        # Record the meeting in the itinerary
        itinerary.append({
            'action': 'meet',
            'location': destination,
            'person': friend['name'],
            'start_time': convert_minutes_to_time(arrival_time),
            'end_time': convert_minutes_to_time(meeting_end_time)
        })

        # Update current time and location for next step
        current_time = meeting_end_time
        current_location = destination

    # Update best itinerary if this permutation is valid and better
    if valid:
        if len(itinerary) > max_visited:
            max_visited = len(itinerary)
            best_itinerary = itinerary

# Output JSON-formatted dictionary
result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))