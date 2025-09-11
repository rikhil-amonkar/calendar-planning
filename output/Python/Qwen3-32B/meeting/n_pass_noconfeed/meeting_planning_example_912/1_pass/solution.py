import heapq
from collections import defaultdict

# Define all locations
locations = [
    'Union Square',
    'Presidio',
    'Alamo Square',
    'Marina District',
    'Financial District',
    'Nob Hill',
    'Sunset District',
    'Chinatown',
    'Russian Hill',
    'North Beach',
    'Haight-Ashbury'
]

# Define friends with their data
friends = [
    {
        'name': 'Kimberly',
        'location': 'Presidio',
        'start': 15 * 60 + 30,  # 3:30 PM
        'end': 16 * 60,         # 4:00 PM
        'duration': 15,
        'index': 0
    },
    {
        'name': 'Elizabeth',
        'location': 'Alamo Square',
        'start': 19 * 60 + 15,  # 7:15 PM
        'end': 20 * 60 + 15,    # 8:15 PM
        'duration': 15,
        'index': 1
    },
    {
        'name': 'Joshua',
        'location': 'Marina District',
        'start': 10 * 60 + 30,  # 10:30 AM
        'end': 14 * 60 + 15,    # 2:15 PM
        'duration': 45,
        'index': 2
    },
    {
        'name': 'Sandra',
        'location': 'Financial District',
        'start': 19 * 60 + 30,  # 7:30 PM
        'end': 20 * 60 + 15,    # 8:15 PM
        'duration': 45,
        'index': 3
    },
    {
        'name': 'Kenneth',
        'location': 'Nob Hill',
        'start': 12 * 60 + 45,  # 12:45 PM
        'end': 21 * 60 + 45,    # 9:45 PM
        'duration': 30,
        'index': 4
    },
    {
        'name': 'Betty',
        'location': 'Sunset District',
        'start': 14 * 60,       # 2:00 PM
        'end': 19 * 60,         # 7:00 PM
        'duration': 60,
        'index': 5
    },
    {
        'name': 'Deborah',
        'location': 'Chinatown',
        'start': 17 * 60 + 15,  # 5:15 PM
        'end': 20 * 60 + 30,    # 8:30 PM
        'duration': 15,
        'index': 6
    },
    {
        'name': 'Barbara',
        'location': 'Russian Hill',
        'start': 17 * 60 + 30,  # 5:30 PM
        'end': 21 * 60 + 15,    # 9:15 PM
        'duration': 120,
        'index': 7
    },
    {
        'name': 'Steven',
        'location': 'North Beach',
        'start': 17 * 60 + 45,  # 5:45 PM
        'end': 20 * 60 + 45,    # 8:45 PM
        'duration': 90,
        'index': 8
    },
    {
        'name': 'Daniel',
        'location': 'Haight-Ashbury',
        'start': 18 * 60 + 30,  # 6:30 PM
        'end': 18 * 60 + 45,    # 6:45 PM
        'duration': 15,
        'index': 9
    }
]

# Precompute friends by location
location_to_friends = defaultdict(list)
for friend in friends:
    location_to_friends[friend['location']].append(friend)

# Define travel times between locations
travel_times = {
    'Union Square': {
        'Presidio': 24,
        'Alamo Square': 15,
        'Marina District': 18,
        'Financial District': 9,
        'Nob Hill': 9,
        'Sunset District': 27,
        'Chinatown': 7,
        'Russian Hill': 13,
        'North Beach': 10,
        'Haight-Ashbury': 18
    },
    'Presidio': {
        'Union Square': 22,
        'Alamo Square': 19,
        'Marina District': 11,
        'Financial District': 23,
        'Nob Hill': 18,
        'Sunset District': 15,
        'Chinatown': 21,
        'Russian Hill': 14,
        'North Beach': 18,
        'Haight-Ashbury': 15
    },
    'Alamo Square': {
        'Union Square': 14,
        'Presidio': 17,
        'Marina District': 15,
        'Financial District': 17,
        'Nob Hill': 11,
        'Sunset District': 16,
        'Chinatown': 15,
        'Russian Hill': 13,
        'North Beach': 15,
        'Haight-Ashbury': 5
    },
    'Marina District': {
        'Union Square': 16,
        'Presidio': 10,
        'Alamo Square': 15,
        'Financial District': 17,
        'Nob Hill': 12,
        'Sunset District': 19,
        'Chinatown': 15,
        'Russian Hill': 8,
        'North Beach': 11,
        'Haight-Ashbury': 16
    },
    'Financial District': {
        'Union Square': 9,
        'Presidio': 22,
        'Alamo Square': 17,
        'Marina District': 15,
        'Nob Hill': 8,
        'Sunset District': 30,
        'Chinatown': 5,
        'Russian Hill': 11,
        'North Beach': 7,
        'Haight-Ashbury': 19
    },
    'Nob Hill': {
        'Union Square': 7,
        'Presidio': 17,
        'Alamo Square': 11,
        'Marina District': 11,
        'Financial District': 9,
        'Sunset District': 24,
        'Chinatown': 6,
        'Russian Hill': 5,
        'North Beach': 8,
        'Haight-Ashbury': 13
    },
    'Sunset District': {
        'Union Square': 30,
        'Presidio': 16,
        'Alamo Square': 17,
        'Marina District': 21,
        'Financial District': 30,
        'Nob Hill': 27,
        'Chinatown': 30,
        'Russian Hill': 24,
        'North Beach': 28,
        'Haight-Ashbury': 15
    },
    'Chinatown': {
        'Union Square': 7,
        'Presidio': 19,
        'Alamo Square': 17,
        'Marina District': 12,
        'Financial District': 5,
        'Nob Hill': 9,
        'Sunset District': 29,
        'Russian Hill': 7,
        'North Beach': 3,
        'Haight-Ashbury': 19
    },
    'Russian Hill': {
        'Union Square': 10,
        'Presidio': 14,
        'Alamo Square': 15,
        'Marina District': 7,
        'Financial District': 11,
        'Nob Hill': 5,
        'Sunset District': 23,
        'Chinatown': 9,
        'North Beach': 5,
        'Haight-Ashbury': 17
    },
    'North Beach': {
        'Union Square': 7,
        'Presidio': 17,
        'Alamo Square': 16,
        'Marina District': 9,
        'Financial District': 8,
        'Nob Hill': 7,
        'Sunset District': 27,
        'Chinatown': 6,
        'Russian Hill': 4,
        'Haight-Ashbury': 18
    },
    'Haight-Ashbury': {
        'Union Square': 19,
        'Presidio': 15,
        'Alamo Square': 5,
        'Marina District': 17,
        'Financial District': 21,
        'Nob Hill': 15,
        'Sunset District': 15,
        'Chinatown': 19,
        'Russian Hill': 17,
        'North Beach': 19
    }
}

# Best arrival times: (location, mask) -> time
best = {}

# Priority queue: (-num_met, current_time, current_location, mask, itinerary)
heap = []
heapq.heappush(heap, (0, 540, 'Union Square', 0, []))  # 9:00 AM is 540 mins

found_solution = None

while heap:
    neg_num_met, current_time, current_location, mask, itinerary = heapq.heappop(heap)
    num_met = -neg_num_met

    # Check if this state is worse than a previously found one for (current_location, mask)
    key = (current_location, mask)
    if key in best:
        if best[key] <= current_time:
            continue  # we already have a better or equal state
    best[key] = current_time

    # Check if this is a better solution than what we have
    if found_solution is None or num_met > -found_solution[0]:
        found_solution = (neg_num_met, current_time, current_location, mask, itinerary)

    # Option 1: Meet a friend at current_location
    for friend in location_to_friends.get(current_location, []):
        friend_index = friend['index']
        if (mask & (1 << friend_index)) != 0:
            continue  # already met this friend

        # Check if current_time allows meeting this friend
        friend_start = friend['start']
        friend_end = friend['end']
        required_duration = friend['duration']

        # The earliest we can start is max(current_time, friend_start)
        earliest_start = max(current_time, friend_start)
        latest_start = friend_end - required_duration

        if earliest_start > latest_start:
            continue  # can't meet this friend

        # Compute the new_time after meeting
        new_time = earliest_start + required_duration

        # Create new mask
        new_mask = mask | (1 << friend_index)

        # Create new itinerary entry
        new_itinerary = itinerary + [{
            'action': 'meet',
            'location': current_location,
            'person': friend['name'],
            'start_time': f"{earliest_start // 60}:{earliest_start % 60:02d}",
            'end_time': f"{new_time // 60}:{new_time % 60:02d}"
        }]

        # Push new state into heap
        new_neg_num_met = -(num_met + 1)
        new_key = (current_location, new_mask)
        heapq.heappush(heap, (new_neg_num_met, new_time, current_location, new_mask, new_itinerary))

    # Option 2: Travel to another location
    for next_location in locations:
        if next_location == current_location:
            continue

        # Calculate travel time
        travel_time = travel_times[current_location][next_location]
        arrival_time = current_time + travel_time

        # Check if this (next_location, mask) is better than existing
        new_key = (next_location, mask)
        if new_key in best and best[new_key] <= arrival_time:
            continue  # we already have a better or equal arrival time for this state

        # Push the new state
        heapq.heappush(heap, (neg_num_met, arrival_time, next_location, mask, itinerary))

# Output the result
import json
if found_solution:
    _, _, _, _, itinerary = found_solution
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))