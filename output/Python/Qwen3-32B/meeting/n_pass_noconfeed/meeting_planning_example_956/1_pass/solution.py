import heapq
import json

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Define travel times between locations
travel_times = {
    'The Castro': {
        'Alamo Square': 8,
        'Richmond District': 16,
        'Financial District': 21,
        'Union Square': 19,
        'Fisherman\'s Wharf': 24,
        'Marina District': 21,
        'Haight-Ashbury': 6,
        'Mission District': 7,
        'Pacific Heights': 16,
        'Golden Gate Park': 11,
    },
    'Alamo Square': {
        'The Castro': 8,
        'Richmond District': 11,
        'Financial District': 17,
        'Union Square': 14,
        'Fisherman\'s Wharf': 19,
        'Marina District': 15,
        'Haight-Ashbury': 5,
        'Mission District': 10,
        'Pacific Heights': 10,
        'Golden Gate Park': 9,
    },
    'Richmond District': {
        'The Castro': 16,
        'Alamo Square': 13,
        'Financial District': 22,
        'Union Square': 21,
        'Fisherman\'s Wharf': 18,
        'Marina District': 9,
        'Haight-Ashbury': 10,
        'Mission District': 20,
        'Pacific Heights': 10,
        'Golden Gate Park': 9,
    },
    'Financial District': {
        'The Castro': 20,
        'Alamo Square': 17,
        'Richmond District': 21,
        'Union Square': 9,
        'Fisherman\'s Wharf': 10,
        'Marina District': 15,
        'Haight-Ashbury': 19,
        'Mission District': 17,
        'Pacific Heights': 13,
        'Golden Gate Park': 23,
    },
    'Union Square': {
        'The Castro': 17,
        'Alamo Square': 15,
        'Richmond District': 20,
        'Financial District': 9,
        'Fisherman\'s Wharf': 15,
        'Marina District': 18,
        'Haight-Ashbury': 18,
        'Mission District': 14,
        'Pacific Heights': 15,
        'Golden Gate Park': 22,
    },
    'Fisherman\'s Wharf': {
        'The Castro': 27,
        'Alamo Square': 21,
        'Richmond District': 18,
        'Financial District': 11,
        'Union Square': 13,
        'Marina District': 9,
        'Haight-Ashbury': 22,
        'Mission District': 22,
        'Pacific Heights': 12,
        'Golden Gate Park': 25,
    },
    'Marina District': {
        'The Castro': 22,
        'Alamo Square': 15,
        'Richmond District': 11,
        'Financial District': 17,
        'Union Square': 16,
        'Fisherman\'s Wharf': 10,
        'Haight-Ashbury': 16,
        'Mission District': 20,
        'Pacific Heights': 7,
        'Golden Gate Park': 18,
    },
    'Haight-Ashbury': {
        'The Castro': 6,
        'Alamo Square': 5,
        'Richmond District': 10,
        'Financial District': 21,
        'Union Square': 19,
        'Fisherman\'s Wharf': 23,
        'Marina District': 17,
        'Mission District': 11,
        'Pacific Heights': 12,
        'Golden Gate Park': 7,
    },
    'Mission District': {
        'The Castro': 7,
        'Alamo Square': 11,
        'Richmond District': 20,
        'Financial District': 15,
        'Union Square': 15,
        'Fisherman\'s Wharf': 22,
        'Marina District': 19,
        'Haight-Ashbury': 12,
        'Pacific Heights': 16,
        'Golden Gate Park': 17,
    },
    'Pacific Heights': {
        'The Castro': 16,
        'Alamo Square': 10,
        'Richmond District': 12,
        'Financial District': 13,
        'Union Square': 12,
        'Fisherman\'s Wharf': 13,
        'Marina District': 6,
        'Haight-Ashbury': 11,
        'Mission District': 15,
        'Golden Gate Park': 15,
    },
    'Golden Gate Park': {
        'The Castro': 13,
        'Alamo Square': 9,
        'Richmond District': 7,
        'Financial District': 26,
        'Union Square': 22,
        'Fisherman\'s Wharf': 24,
        'Marina District': 16,
        'Haight-Ashbury': 7,
        'Mission District': 17,
        'Pacific Heights': 16,
    },
}

# Define friends' constraints
friends = [
    {
        'name': 'William',
        'location': 'Alamo Square',
        'start': 915,  # 3:15 PM
        'end': 1035,   # 5:15 PM
        'duration': 60
    },
    {
        'name': 'Joshua',
        'location': 'Richmond District',
        'start': 420,   # 7:00 AM
        'end': 1200,    # 8:00 PM
        'duration': 15
    },
    {
        'name': 'Joseph',
        'location': 'Financial District',
        'start': 675,   # 11:15 AM
        'end': 810,     # 1:30 PM
        'duration': 15
    },
    {
        'name': 'David',
        'location': 'Union Square',
        'start': 1005,  # 4:45 PM
        'end': 1155,    # 7:15 PM
        'duration': 45
    },
    {
        'name': 'Brian',
        'location': 'Fisherman\'s Wharf',
        'start': 825,   # 1:45 PM
        'end': 1245,    # 8:45 PM
        'duration': 105
    },
    {
        'name': 'Karen',
        'location': 'Marina District',
        'start': 690,   # 11:30 AM
        'end': 1110,    # 6:30 PM
        'duration': 15
    },
    {
        'name': 'Anthony',
        'location': 'Haight-Ashbury',
        'start': 435,   # 7:15 AM
        'end': 630,     # 10:30 AM
        'duration': 30
    },
    {
        'name': 'Matthew',
        'location': 'Mission District',
        'start': 1035,  # 5:15 PM
        'end': 1155,    # 7:15 PM
        'duration': 120
    },
    {
        'name': 'Helen',
        'location': 'Pacific Heights',
        'start': 480,   # 8:00 AM
        'end': 720,     # 12:00 PM
        'duration': 75
    },
    {
        'name': 'Jeffrey',
        'location': 'Golden Gate Park',
        'start': 1140,  # 7:00 PM
        'end': 1290,    # 9:30 PM
        'duration': 60
    }
]

# Initialize the priority queue
initial_location = 'The Castro'
initial_time = 540  # 9:00 AM
initial_mask = 0
initial_path = []

heap = []
heapq.heappush(heap, (0, initial_time, initial_location, initial_mask, initial_path))

visited = {}  # (location, mask) -> earliest_time

best_state = None

while heap:
    priority, current_time, current_location, mask, path = heapq.heappop(heap)
    num_friends = -priority  # since priority is -num_friends

    # Update best_state if this is the best so far
    if best_state is None or num_friends > best_state[0]:
        best_state = (num_friends, current_time, current_location, mask, path)
    elif num_friends == best_state[0] and current_time < best_state[1]:
        best_state = (num_friends, current_time, current_location, mask, path)

    # Skip if this state is not the best for (current_location, mask)
    key = (current_location, mask)
    if key in visited:
        if current_time >= visited[key]:
            continue
    visited[key] = current_time

    # Try to meet each friend not yet met
    for i, friend in enumerate(friends):
        if not (mask & (1 << i)):
            friend_loc = friend['location']
            friend_start = friend['start']
            friend_end = friend['end']
            duration = friend['duration']

            # Calculate travel time
            if current_location == friend_loc:
                travel_time = 0
            else:
                travel_time = travel_times[current_location][friend_loc]

            arrival_time = current_time + travel_time

            # Check if arrival time allows the meeting
            if arrival_time >= friend_start and arrival_time + duration <= friend_end:
                new_time = arrival_time + duration
                new_mask = mask | (1 << i)
                new_location = friend_loc
                new_path = path + [(friend, arrival_time, new_time)]

                # Check if this new state is better than existing ones
                new_key = (new_location, new_mask)
                if new_key not in visited or new_time < visited.get(new_key, float('inf')):
                    visited[new_key] = new_time
                    new_priority = - (num_friends + 1)
                    heapq.heappush(heap, (new_priority, new_time, new_location, new_mask, new_path))

# Generate the itinerary from the best state
num_friends_met, end_time, final_location, final_mask, best_path = best_state
itinerary = []
for entry in best_path:
    friend, start_time, end_time = entry
    itinerary.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": minutes_to_time(start_time),
        "end_time": minutes_to_time(end_time)
    })

# Output the JSON result
print(json.dumps({"itinerary": itinerary}, indent=2))