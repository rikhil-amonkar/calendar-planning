import itertools
import json

def time_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define travel times between locations
travel_times = {
    'Bayview': {
        'North Beach': 21,
        'Presidio': 31,
        'Haight-Ashbury': 19,
        'Union Square': 17,
    },
    'North Beach': {
        'Bayview': 22,
        'Presidio': 17,
        'Haight-Ashbury': 18,
        'Union Square': 7,
    },
    'Presidio': {
        'Bayview': 31,
        'North Beach': 18,
        'Haight-Ashbury': 15,
        'Union Square': 22,
    },
    'Haight-Ashbury': {
        'Bayview': 18,
        'North Beach': 19,
        'Presidio': 15,
        'Union Square': 17,
    },
    'Union Square': {
        'Bayview': 15,
        'North Beach': 10,
        'Presidio': 24,
        'Haight-Ashbury': 18,
    },
}

# Define friends' constraints
friends = [
    {
        'name': 'Kimberly',
        'location': 'Union Square',
        'available_start': 7 * 60 + 45,  # 7:45 AM
        'available_end': 16 * 60 + 45,    # 4:45 PM
        'required_duration': 30,
    },
    {
        'name': 'Margaret',
        'location': 'Presidio',
        'available_start': 10 * 60 + 15,  # 10:15 AM
        'available_end': 15 * 60 + 15,    # 3:15 PM
        'required_duration': 30,
    },
    {
        'name': 'Barbara',
        'location': 'North Beach',
        'available_start': 13 * 60 + 45,  # 1:45 PM
        'available_end': 20 * 60 + 15,    # 8:15 PM
        'required_duration': 60,
    },
    {
        'name': 'Kevin',
        'location': 'Haight-Ashbury',
        'available_start': 20 * 60,       # 8:00 PM
        'available_end': 20 * 60 + 45,    # 8:45 PM
        'required_duration': 30,
    },
]

max_friends = 0
best_itinerary = []

# Check all permutations of friends for lengths 1 to 4
for r in range(1, 5):
    for perm in itertools.permutations(friends, r):
        current_time = 9 * 60  # 9:00 AM in minutes
        current_location = 'Bayview'
        itinerary = []
        valid = True

        for friend in perm:
            # Get travel time from current location to friend's location
            if current_location not in travel_times or friend['location'] not in travel_times[current_location]:
                valid = False
                break
            travel_time = travel_times[current_location][friend['location']]
            arrival_time = current_time + travel_time

            # Determine earliest possible meeting start time
            start_time = max(arrival_time, friend['available_start'])

            # Check if meeting can be scheduled
            end_time = start_time + friend['required_duration']
            if end_time > friend['available_end']:
                valid = False
                break

            # Add to itinerary
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': time_to_str(start_time),
                'end_time': time_to_str(end_time),
            })

            # Update current time and location
            current_time = end_time
            current_location = friend['location']

        if valid:
            if len(itinerary) > max_friends:
                max_friends = len(itinerary)
                best_itinerary = itinerary
            elif len(itinerary) == max_friends and max_friends > 0:
                # For ties, we can keep the first one found
                pass

# Output the result as JSON
result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))