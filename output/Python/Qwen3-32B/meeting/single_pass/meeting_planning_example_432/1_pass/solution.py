import itertools
import json
from copy import deepcopy

def minutes_to_time_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

# Define friends with their meeting constraints
friends = [
    {
        'name': 'Joseph',
        'location': "Fisherman's Wharf",
        'start': 8 * 60,  # 8:00 AM
        'end': 17 * 60 + 30,  # 5:30 PM
        'min_duration': 90
    },
    {
        'name': 'Jeffrey',
        'location': 'Bayview',
        'start': 17 * 60 + 30,  # 5:30 PM
        'end': 21 * 60 + 30,  # 9:30 PM
        'min_duration': 60
    },
    {
        'name': 'Kevin',
        'location': 'Mission District',
        'start': 11 * 60 + 15,  # 11:15 AM
        'end': 15 * 60 + 15,  # 3:15 PM
        'min_duration': 30
    },
    {
        'name': 'David',
        'location': 'Embarcadero',
        'start': 8 * 60 + 15,  # 8:15 AM
        'end': 9 * 60,  # 9:00 AM
        'min_duration': 30
    },
    {
        'name': 'Barbara',
        'location': 'Financial District',
        'start': 10 * 60 + 30,  # 10:30 AM
        'end': 16 * 60 + 30,  # 4:30 PM
        'min_duration': 15
    }
]

# Define travel times between locations
travel_times = {
    'Golden Gate Park': {
        "Fisherman's Wharf": 24,
        'Bayview': 23,
        'Mission District': 17,
        'Embarcadero': 25,
        'Financial District': 26
    },
    "Fisherman's Wharf": {
        'Golden Gate Park': 25,
        'Bayview': 26,
        'Mission District': 22,
        'Embarcadero': 8,
        'Financial District': 11
    },
    'Bayview': {
        'Golden Gate Park': 22,
        "Fisherman's Wharf": 25,
        'Mission District': 13,
        'Embarcadero': 19,
        'Financial District': 19
    },
    'Mission District': {
        'Golden Gate Park': 17,
        "Fisherman's Wharf": 22,
        'Bayview': 15,
        'Embarcadero': 19,
        'Financial District': 17
    },
    'Embarcadero': {
        'Golden Gate Park': 25,
        "Fisherman's Wharf": 6,
        'Bayview': 21,
        'Mission District': 20,
        'Financial District': 5
    },
    'Financial District': {
        'Golden Gate Park': 23,
        "Fisherman's Wharf": 10,
        'Bayview': 19,
        'Mission District': 17,
        'Embarcadero': 4
    }
}

best_itinerary = []
max_length = 0

# Check all possible permutations of friends
for r in range(1, len(friends) + 1):
    for subset in itertools.combinations(friends, r):
        for perm in itertools.permutations(subset):
            # Simulate this permutation
            current_time = 9 * 60  # 9:00 AM in minutes
            current_location = 'Golden Gate Park'
            itinerary = []
            valid = True

            for friend in perm:
                # Calculate travel time
                next_location = friend['location']
                travel_time = travel_times[current_location][next_location]
                arrival_time = current_time + travel_time

                # Determine meeting start time
                meeting_start = max(arrival_time, friend['start'])
                meeting_end = meeting_start + friend['min_duration']

                # Check if meeting end time is within friend's availability
                if meeting_end > friend['end']:
                    valid = False
                    break

                # Add to itinerary
                itinerary.append({
                    'action': 'meet',
                    'location': next_location,
                    'person': friend['name'],
                    'start_time': minutes_to_time_str(meeting_start),
                    'end_time': minutes_to_time_str(meeting_end)
                })

                # Update current time and location
                current_time = meeting_end
                current_location = next_location

            if valid:
                if len(itinerary) > max_length:
                    max_length = len(itinerary)
                    best_itinerary = deepcopy(itinerary)
                elif len(itinerary) == max_length and max_length > 0:
                    # Optional: choose the first one if there are multiple with same length
                    pass  # Keep the first one found

# Output the best itinerary as JSON
result = {
    "itinerary": best_itinerary
}

print(json.dumps(result))