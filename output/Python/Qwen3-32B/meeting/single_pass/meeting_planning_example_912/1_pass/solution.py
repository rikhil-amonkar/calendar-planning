import heapq
import json

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
        'Haight-Ashbury': 18,
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
        'Haight-Ashbury': 15,
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
        'Haight-Ashbury': 5,
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
        'Haight-Ashbury': 16,
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
        'Haight-Ashbury': 19,
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
        'Haight-Ashbury': 13,
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
        'Haight-Ashbury': 15,
    },
    'Chinatown': {
        'Union Square': 7,
        'Presidio': 19,
        'Alamo Square': 17,
        'Marina District': 12,
        'Financial District': 5,
        'Nob Hill': 9,
        'Sunset District': 30,
        'Russian Hill': 9,
        'North Beach': 3,
        'Haight-Ashbury': 19,
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
        'Haight-Ashbury': 17,
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
        'Haight-Ashbury': 18,
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
        'North Beach': 19,
    }
}

# Define friends' constraints
friends = [
    {
        'name': 'Kimberly',
        'location': 'Presidio',
        'available_start': 15 * 60 + 30,  # 3:30 PM
        'available_end': 16 * 60,          # 4:00 PM
        'min_duration': 15,
    },
    {
        'name': 'Elizabeth',
        'location': 'Alamo Square',
        'available_start': 19 * 60 + 15,   # 7:15 PM
        'available_end': 20 * 60 + 15,     # 8:15 PM
        'min_duration': 15,
    },
    {
        'name': 'Joshua',
        'location': 'Marina District',
        'available_start': 10 * 60 + 30,   # 10:30 AM
        'available_end': 14 * 60 + 15,     # 2:15 PM
        'min_duration': 45,
    },
    {
        'name': 'Sandra',
        'location': 'Financial District',
        'available_start': 19 * 60 + 30,   # 7:30 PM
        'available_end': 20 * 60 + 15,     # 8:15 PM
        'min_duration': 45,
    },
    {
        'name': 'Kenneth',
        'location': 'Nob Hill',
        'available_start': 12 * 60 + 45,   # 12:45 PM
        'available_end': 21 * 60 + 45,     # 9:45 PM
        'min_duration': 30,
    },
    {
        'name': 'Betty',
        'location': 'Sunset District',
        'available_start': 14 * 60,        # 2:00 PM
        'available_end': 19 * 60,          # 7:00 PM
        'min_duration': 60,
    },
    {
        'name': 'Deborah',
        'location': 'Chinatown',
        'available_start': 17 * 60 + 15,   # 5:15 PM
        'available_end': 20 * 60 + 30,     # 8:30 PM
        'min_duration': 15,
    },
    {
        'name': 'Barbara',
        'location': 'Russian Hill',
        'available_start': 17 * 60 + 30,   # 5:30 PM
        'available_end': 21 * 60 + 15,     # 9:15 PM
        'min_duration': 120,
    },
    {
        'name': 'Steven',
        'location': 'North Beach',
        'available_start': 17 * 60 + 45,   # 5:45 PM
        'available_end': 20 * 60 + 45,     # 8:45 PM
        'min_duration': 90,
    },
    {
        'name': 'Daniel',
        'location': 'Haight-Ashbury',
        'available_start': 18 * 60 + 30,   # 6:30 PM
        'available_end': 18 * 60 + 45,     # 6:45 PM
        'min_duration': 15,
    },
]

# Precompute earliest and latest start times for each friend
for friend in friends:
    friend['earliest_start'] = friend['available_start']
    friend['latest_start'] = friend['available_end'] - friend['min_duration']

n_friends = len(friends)

# Initialize the priority queue
heap = []
heapq.heappush(heap, (0, 540, 'Union Square', 0, []))  # (priority, current_time, current_location, mask, itinerary)

best = {}
best_itinerary = []

while heap:
    priority, current_time, current_location, mask, itinerary = heapq.heappop(heap)
    num_friends = -priority  # since priority is -num_friends

    # Check if this state is worse than a previously recorded state
    key = (mask, current_location)
    if key in best:
        if best[key] <= current_time:
            continue
    best[key] = current_time

    # Update the best itinerary if this one is better
    if len(itinerary) > len(best_itinerary):
        best_itinerary = itinerary

    # Check if all friends are visited
    if num_friends == n_friends:
        break

    # Try to visit each unvisited friend
    for i in range(n_friends):
        if not (mask & (1 << i)):
            friend = friends[i]
            loc = friend['location']
            earliest_start = friend['earliest_start']
            latest_start = friend['latest_start']
            duration = friend['min_duration']

            # Compute travel time from current_location to loc
            travel_time = travel_times[current_location][loc]
            arrival_time = current_time + travel_time

            # Check if arrival_time is <= latest_start
            if arrival_time > latest_start:
                continue  # cannot make it in time

            # Compute the start time: max(arrival_time, earliest_start)
            start_time = max(arrival_time, earliest_start)
            end_time = start_time + duration

            # Check if end_time <= available_end
            if end_time > friend['available_end']:
                continue  # shouldn't happen

            # Create new mask
            new_mask = mask | (1 << i)

            # Create new itinerary
            new_itinerary = itinerary + [{
                'action': 'meet',
                'location': loc,
                'person': friend['name'],
                'start_time': f"{start_time // 60}:{start_time % 60:02d}",
                'end_time': f"{end_time // 60}:{end_time % 60:02d}"
            }]

            # Push the new state into the heap
            heapq.heappush(heap, (
                -(num_friends + 1),
                end_time,
                loc,
                new_mask,
                new_itinerary
            ))

# Output the best itinerary as JSON
print(json.dumps({"itinerary": best_itinerary}, indent=2))