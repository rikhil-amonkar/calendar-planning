import heapq
import json

def time_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define friends
friends = [
    {
        'name': 'Nancy',
        'location': 'Nob Hill',
        'start_time': 8 * 60 + 15,  # 495
        'end_time': 12 * 60 + 45,   # 765
        'required': 90
    },
    {
        'name': 'Stephanie',
        'location': 'Haight-Ashbury',
        'start_time': 10 * 60 + 15, # 615
        'end_time': 12 * 60 + 15,   # 735
        'required': 75
    },
    {
        'name': 'David',
        'location': 'Marina District',
        'start_time': 11 * 60 + 15, # 675
        'end_time': 13 * 60 + 15,   # 795
        'required': 120
    },
    {
        'name': 'Elizabeth',
        'location': 'Union Square',
        'start_time': 11 * 60 + 30, # 690
        'end_time': 21 * 60,        # 1260
        'required': 60
    },
    {
        'name': 'Robert',
        'location': 'Financial District',
        'start_time': 13 * 60 + 15, # 795
        'end_time': 15 * 60 + 15,   # 915
        'required': 45
    },
    {
        'name': 'Melissa',
        'location': 'Richmond District',
        'start_time': 14 * 60,      # 840
        'end_time': 19 * 60 + 30,   # 1170
        'required': 30
    },
    {
        'name': 'Brian',
        'location': 'Embarcadero',
        'start_time': 14 * 60 + 15, # 855
        'end_time': 16 * 60,        # 960
        'required': 105
    },
    {
        'name': 'James',
        'location': 'Presidio',
        'start_time': 15 * 60,      # 900
        'end_time': 18 * 60 + 15,   # 1095
        'required': 120
    },
    {
        'name': 'Steven',
        'location': 'North Beach',
        'start_time': 17 * 60 + 30, # 1050
        'end_time': 20 * 60 + 30,   # 1230
        'required': 15
    },
    {
        'name': 'Sarah',
        'location': 'Golden Gate Park',
        'start_time': 17 * 60,      # 1020
        'end_time': 19 * 60 + 15,   # 1155
        'required': 75
    },
]

# Define travel times between locations
travel_times = {
    'The Castro': {
        'North Beach': 20,
        'Golden Gate Park': 11,
        'Embarcadero': 22,
        'Haight-Ashbury': 6,
        'Richmond District': 16,
        'Nob Hill': 16,
        'Marina District': 21,
        'Presidio': 20,
        'Union Square': 19,
        'Financial District': 21,
    },
    'North Beach': {
        'The Castro': 23,
        'Golden Gate Park': 22,
        'Embarcadero': 6,
        'Haight-Ashbury': 18,
        'Richmond District': 18,
        'Nob Hill': 7,
        'Marina District': 9,
        'Presidio': 17,
        'Union Square': 7,
        'Financial District': 8,
    },
    'Golden Gate Park': {
        'The Castro': 13,
        'North Beach': 23,
        'Embarcadero': 25,
        'Haight-Ashbury': 7,
        'Richmond District': 7,
        'Nob Hill': 20,
        'Marina District': 16,
        'Presidio': 11,
        'Union Square': 22,
        'Financial District': 26,
    },
    'Embarcadero': {
        'The Castro': 25,
        'North Beach': 5,
        'Golden Gate Park': 25,
        'Haight-Ashbury': 21,
        'Richmond District': 21,
        'Nob Hill': 10,
        'Marina District': 12,
        'Presidio': 20,
        'Union Square': 10,
        'Financial District': 5,
    },
    'Haight-Ashbury': {
        'The Castro': 6,
        'North Beach': 19,
        'Golden Gate Park': 7,
        'Embarcadero': 20,
        'Richmond District': 10,
        'Nob Hill': 15,
        'Marina District': 17,
        'Presidio': 15,
        'Union Square': 19,
        'Financial District': 21,
    },
    'Richmond District': {
        'The Castro': 16,
        'North Beach': 17,
        'Golden Gate Park': 9,
        'Embarcadero': 19,
        'Haight-Ashbury': 10,
        'Nob Hill': 17,
        'Marina District': 9,
        'Presidio': 7,
        'Union Square': 21,
        'Financial District': 22,
    },
    'Nob Hill': {
        'The Castro': 17,
        'North Beach': 8,
        'Golden Gate Park': 17,
        'Embarcadero': 9,
        'Haight-Ashbury': 13,
        'Richmond District': 14,
        'Marina District': 11,
        'Presidio': 17,
        'Union Square': 7,
        'Financial District': 9,
    },
    'Marina District': {
        'The Castro': 22,
        'North Beach': 11,
        'Golden Gate Park': 18,
        'Embarcadero': 14,
        'Haight-Ashbury': 16,
        'Richmond District': 11,
        'Nob Hill': 12,
        'Presidio': 10,
        'Union Square': 16,
        'Financial District': 17,
    },
    'Presidio': {
        'The Castro': 21,
        'North Beach': 18,
        'Golden Gate Park': 12,
        'Embarcadero': 20,
        'Haight-Ashbury': 15,
        'Richmond District': 7,
        'Nob Hill': 18,
        'Marina District': 11,
        'Union Square': 22,
        'Financial District': 23,
    },
    'Union Square': {
        'The Castro': 17,
        'North Beach': 10,
        'Golden Gate Park': 22,
        'Embarcadero': 11,
        'Haight-Ashbury': 18,
        'Richmond District': 20,
        'Nob Hill': 9,
        'Marina District': 18,
        'Presidio': 24,
        'Financial District': 9,
    },
    'Financial District': {
        'The Castro': 20,
        'North Beach': 7,
        'Golden Gate Park': 23,
        'Embarcadero': 4,
        'Haight-Ashbury': 19,
        'Richmond District': 21,
        'Nob Hill': 8,
        'Marina District': 15,
        'Presidio': 22,
        'Union Square': 9,
    },
}

# Initial state: at The Castro, time 9:00 AM (540 minutes)
initial_location = 'The Castro'
initial_time = 9 * 60  # 540 minutes

# Priority queue: (-num_friends, current_time, current_location, mask, itinerary)
heap = []
heapq.heappush(heap, (0, initial_time, initial_location, 0, []))

# Cache to avoid revisiting worse states
cache = {}

best_itinerary = []
best_count = 0

while heap:
    neg_count, current_time, current_loc, mask, itinerary = heapq.heappop(heap)
    current_count = -neg_count

    # Check if this state is already processed with a better count
    key = (current_loc, current_time, mask)
    if key in cache and cache[key] >= current_count:
        continue
    cache[key] = current_count

    # Update best itinerary if this is better
    if current_count > best_count:
        best_count = current_count
        best_itinerary = itinerary

    # Try to visit each friend not yet visited
    for friend_idx in range(len(friends)):
        if mask & (1 << friend_idx):
            continue  # Already visited
        friend = friends[friend_idx]
        dest_loc = friend['location']
        # Check if travel is possible
        travel_time = travel_times.get(current_loc, {}).get(dest_loc, float('inf'))
        if travel_time == float('inf'):
            continue  # No direct route

        arrival_time = current_time + travel_time
        friend_start = friend['start_time']
        friend_end = friend['end_time']
        required = friend['required']

        # Calculate possible start and end times
        start_meeting = max(arrival_time, friend_start)
        end_meeting = start_meeting + required

        if end_meeting > friend_end:
            continue  # Can't meet this friend

        # Valid, can proceed
        new_time = end_meeting
        new_mask = mask | (1 << friend_idx)
        new_itinerary = itinerary.copy()
        new_itinerary.append({
            'action': 'meet',
            'location': dest_loc,
            'person': friend['name'],
            'start_time': time_to_str(start_meeting),
            'end_time': time_to_str(new_time),
        })

        # Push new state to heap
        new_neg_count = - (current_count + 1)
        heapq.heappush(heap, (new_neg_count, new_time, dest_loc, new_mask, new_itinerary))

# Output the best itinerary as JSON
result = {
    "itinerary": best_itinerary
}
print(json.dumps(result, indent=2))