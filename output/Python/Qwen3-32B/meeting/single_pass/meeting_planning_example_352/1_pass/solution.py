import heapq
import json

# Define travel times between locations
travel_times = {
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Haight-Ashbury'): 18,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Marina District'): 18,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Chinatown'): 6,
    ('Nob Hill', 'Marina District'): 11,
    ('Haight-Ashbury', 'Union Square'): 17,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Chinatown'): 19,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Nob Hill'): 8,
    ('Chinatown', 'Haight-Ashbury'): 19,
    ('Chinatown', 'Marina District'): 12,
    ('Marina District', 'Union Square'): 16,
    ('Marina District', 'Nob Hill'): 12,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Chinatown'): 16,
}

# Define friends with their constraints
friends = [
    {
        'name': 'Karen',
        'location': 'Nob Hill',
        'available_start': 555,  # 9:15 AM
        'available_end': 585,    # 9:45 AM
        'required_duration': 30,
    },
    {
        'name': 'Joseph',
        'location': 'Haight-Ashbury',
        'available_start': 750,  # 12:30 PM
        'available_end': 1185,   # 7:45 PM
        'required_duration': 90,
    },
    {
        'name': 'Sandra',
        'location': 'Chinatown',
        'available_start': 435,  # 7:15 AM
        'available_end': 1155,   # 7:15 PM
        'required_duration': 75,
    },
    {
        'name': 'Nancy',
        'location': 'Marina District',
        'available_start': 660,  # 11:00 AM
        'available_end': 1215,   # 8:15 PM
        'required_duration': 105,
    },
]

# Generate valid meeting intervals for each friend
valid_intervals = []
for friend in friends:
    start = friend['available_start']
    end = friend['available_end']
    duration = friend['required_duration']
    friend_intervals = []
    max_start = end - duration
    if max_start >= start:
        for s in range(start, max_start + 1):
            friend_intervals.append((s, s + duration))
    valid_intervals.append(friend_intervals)

# Convert minutes to time string (H:MM)
def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Initialize priority queue and visited set
heap = []
heapq.heappush(heap, (0, 540, 'Union Square', 0, []))  # (priority, current_time, location, bitmask, path)
visited = {}
best_path = None
max_friends = 0

while heap:
    priority, current_time, current_location, bitmask, path = heapq.heappop(heap)
    current_friends = -priority  # since priority is -friends_met

    # Check if this state has been processed with better or equal friends_met
    key = (current_location, bitmask)
    if key in visited:
        if visited[key] >= current_friends:
            continue
    visited[key] = current_friends

    # Update best path if this has more friends
    if current_friends > max_friends:
        max_friends = current_friends
        best_path = path
    elif current_friends == max_friends:
        # For simplicity, keep the first one found
        pass

    # Try to meet each friend not yet met
    for friend_idx in range(len(friends)):
        if not (bitmask & (1 << friend_idx)):
            friend = friends[friend_idx]
            friend_loc = friend['location']
            intervals = valid_intervals[friend_idx]
            for s, e in intervals:
                # Calculate travel time from current_location to friend_loc
                travel_time = travel_times.get((current_location, friend_loc), float('inf'))
                arrival_time = current_time + travel_time
                if arrival_time <= s and e <= friend['available_end']:
                    new_time = e
                    new_bitmask = bitmask | (1 << friend_idx)
                    new_path = path + [(friend_idx, s, e)]
                    new_priority = -(current_friends + 1)
                    heapq.heappush(heap, (new_priority, new_time, friend_loc, new_bitmask, new_path))

# Generate the itinerary from best_path
itinerary = []
if best_path:
    # Sort the path by start time
    sorted_path = sorted(best_path, key=lambda x: x[1])
    for friend_idx, start, end in sorted_path:
        friend = friends[friend_idx]
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": to_time_str(start),
            "end_time": to_time_str(end)
        })

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))