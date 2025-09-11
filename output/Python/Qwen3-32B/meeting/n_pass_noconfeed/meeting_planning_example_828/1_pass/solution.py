import heapq
import json

# Define travel times between locations
travel_times = {
    'Marina District': {
        'Richmond District': 11,
        'Union Square': 16,
        'Nob Hill': 12,
        'Fisherman\'s Wharf': 10,
        'Golden Gate Park': 18,
        'Embarcadero': 14,
        'Financial District': 17,
        'North Beach': 11,
        'Presidio': 10,
    },
    'Richmond District': {
        'Marina District': 9,
        'Union Square': 21,
        'Nob Hill': 17,
        'Fisherman\'s Wharf': 18,
        'Golden Gate Park': 9,
        'Embarcadero': 19,
        'Financial District': 22,
        'North Beach': 17,
        'Presidio': 7,
    },
    'Union Square': {
        'Marina District': 18,
        'Richmond District': 20,
        'Nob Hill': 9,
        'Fisherman\'s Wharf': 15,
        'Golden Gate Park': 22,
        'Embarcadero': 11,
        'Financial District': 9,
        'North Beach': 10,
        'Presidio': 24,
    },
    'Nob Hill': {
        'Marina District': 11,
        'Richmond District': 14,
        'Union Square': 7,
        'Fisherman\'s Wharf': 10,
        'Golden Gate Park': 17,
        'Embarcadero': 9,
        'Financial District': 9,
        'North Beach': 8,
        'Presidio': 17,
    },
    'Fisherman\'s Wharf': {
        'Marina District': 9,
        'Richmond District': 18,
        'Union Square': 13,
        'Nob Hill': 11,
        'Golden Gate Park': 25,
        'Embarcadero': 8,
        'Financial District': 11,
        'North Beach': 6,
        'Presidio': 17,
    },
    'Golden Gate Park': {
        'Marina District': 16,
        'Richmond District': 7,
        'Union Square': 22,
        'Nob Hill': 20,
        'Fisherman\'s Wharf': 24,
        'Embarcadero': 25,
        'Financial District': 26,
        'North Beach': 23,
        'Presidio': 11,
    },
    'Embarcadero': {
        'Marina District': 12,
        'Richmond District': 21,
        'Union Square': 10,
        'Nob Hill': 10,
        'Fisherman\'s Wharf': 6,
        'Golden Gate Park': 25,
        'Financial District': 5,
        'North Beach': 5,
        'Presidio': 20,
    },
    'Financial District': {
        'Marina District': 15,
        'Richmond District': 21,
        'Union Square': 9,
        'Nob Hill': 8,
        'Fisherman\'s Wharf': 10,
        'Golden Gate Park': 23,
        'Embarcadero': 4,
        'North Beach': 7,
        'Presidio': 22,
    },
    'North Beach': {
        'Marina District': 9,
        'Richmond District': 18,
        'Union Square': 7,
        'Nob Hill': 7,
        'Fisherman\'s Wharf': 5,
        'Golden Gate Park': 22,
        'Embarcadero': 6,
        'Financial District': 8,
        'Presidio': 17,
    },
    'Presidio': {
        'Marina District': 11,
        'Richmond District': 7,
        'Union Square': 22,
        'Nob Hill': 18,
        'Fisherman\'s Wharf': 19,
        'Golden Gate Park': 12,
        'Embarcadero': 20,
        'Financial District': 23,
        'North Beach': 18,
    },
}

# Define friends with their details
friends = [
    {
        'name': 'Sandra',
        'location': 'North Beach',
        'start_time': '10:00',
        'end_time': '12:30',
        'duration': 15
    },
    {
        'name': 'William',
        'location': 'Union Square',
        'start_time': '10:45',
        'end_time': '17:30',
        'duration': 45
    },
    {
        'name': 'Elizabeth',
        'location': 'Nob Hill',
        'start_time': '12:15',
        'end_time': '15:00',
        'duration': 105
    },
    {
        'name': 'Joseph',
        'location': 'Fisherman\'s Wharf',
        'start_time': '12:45',
        'end_time': '14:00',
        'duration': 75
    },
    {
        'name': 'Anthony',
        'location': 'Golden Gate Park',
        'start_time': '13:00',
        'end_time': '20:30',
        'duration': 75
    },
    {
        'name': 'Barbara',
        'location': 'Embarcadero',
        'start_time': '19:15',
        'end_time': '20:30',
        'duration': 75
    },
    {
        'name': 'Stephanie',
        'location': 'Richmond District',
        'start_time': '16:15',
        'end_time': '21:30',
        'duration': 75
    },
    {
        'name': 'Carol',
        'location': 'Financial District',
        'start_time': '11:45',
        'end_time': '16:15',
        'duration': 60
    },
    {
        'name': 'Kenneth',
        'location': 'Presidio',
        'start_time': '21:15',
        'end_time': '22:15',
        'duration': 45
    },
]

# Convert time strings to minutes since midnight
for friend in friends:
    h, m = map(int, friend['start_time'].split(':'))
    friend['start_minutes'] = h * 60 + m
    h, m = map(int, friend['end_time'].split(':'))
    friend['end_minutes'] = h * 60 + m
    friend['latest_arrival'] = friend['end_minutes'] - friend['duration']

# Assign indices to friends
for i, friend in enumerate(friends):
    friend['index'] = i

# Starting time and location
start_time_minutes = 9 * 60  # 9:00 AM
start_location = 'Marina District'

# Priority queue: entries are (-num_met, current_time, current_location, bitmask, itinerary)
heap = []
heapq.heappush(heap, (0, start_time_minutes, start_location, 0, []))

# Memoization dictionary: (location, bitmask) -> earliest_time
memo = {}

best_itinerary = []

while heap:
    priority, current_time, current_location, bitmask, itinerary = heapq.heappop(heap)
    num_met = -priority  # because priority is -num_met

    # Check if this state is worse than a previously recorded one
    key = (current_location, bitmask)
    if key in memo:
        if memo[key] <= current_time:
            continue
    memo[key] = current_time

    # Update best itinerary if this has more friends met than previous
    if len(itinerary) > len(best_itinerary):
        best_itinerary = itinerary

    # For each friend not yet met
    for friend in friends:
        if not (bitmask & (1 << friend['index'])):
            # Calculate travel time from current location to friend's location
            if friend['location'] not in travel_times[current_location]:
                continue
            travel_time = travel_times[current_location][friend['location']]
            arrival_time = current_time + travel_time
            adjusted_arrival_time = max(arrival_time, friend['start_minutes'])

            # Check if adjusted arrival time allows meeting
            if adjusted_arrival_time <= friend['latest_arrival']:
                # Can meet this friend
                meeting_start = adjusted_arrival_time
                meeting_end = meeting_start + friend['duration']
                new_bitmask = bitmask | (1 << friend['index'])
                new_location = friend['location']
                new_itinerary = itinerary + [{
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': f"{meeting_start // 60}:{meeting_start % 60:02d}",
                    'end_time': f"{meeting_end // 60}:{meeting_end % 60:02d}"
                }]
                new_priority = -(num_met + 1)
                heapq.heappush(heap, (new_priority, meeting_end, new_location, new_bitmask, new_itinerary))

# Output the best itinerary as JSON
print(json.dumps({"itinerary": best_itinerary}, indent=2))