import heapq
import json

# Define friends and their constraints
friends = [
    {
        'name': 'Nancy',
        'location': 'Nob Hill',
        'available_start': 495,  # 8:15 AM
        'available_end': 765,    # 12:45 PM
        'required_duration': 90
    },
    {
        'name': 'Stephanie',
        'location': 'Haight-Ashbury',
        'available_start': 615,  # 10:15 AM
        'available_end': 735,    # 12:15 PM
        'required_duration': 75
    },
    {
        'name': 'David',
        'location': 'Marina District',
        'available_start': 675,  # 11:15 AM
        'available_end': 795,    # 1:15 PM
        'required_duration': 120
    },
    {
        'name': 'Elizabeth',
        'location': 'Union Square',
        'available_start': 690,  # 11:30 AM
        'available_end': 1080,   # 9:00 PM
        'required_duration': 60
    },
    {
        'name': 'Robert',
        'location': 'Financial District',
        'available_start': 795,  # 1:15 PM
        'available_end': 855,    # 3:15 PM
        'required_duration': 45
    },
    {
        'name': 'Brian',
        'location': 'Embarcadero',
        'available_start': 855,  # 2:15 PM
        'available_end': 900,    # 4:00 PM
        'required_duration': 105
    },
    {
        'name': 'Melissa',
        'location': 'Richmond District',
        'available_start': 840,  # 2:00 PM
        'available_end': 930,    # 7:30 PM
        'required_duration': 30
    },
    {
        'name': 'James',
        'location': 'Presidio',
        'available_start': 900,  # 3:00 PM
        'available_end': 975,    # 6:15 PM
        'required_duration': 120
    },
    {
        'name': 'Sarah',
        'location': 'Golden Gate Park',
        'available_start': 1020, # 5:00 PM
        'available_end': 1155,   # 7:15 PM
        'required_duration': 75
    },
    {
        'name': 'Steven',
        'location': 'North Beach',
        'available_start': 1050, # 5:30 PM
        'available_end': 1230,   # 8:30 PM
        'required_duration': 15
    }
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

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Initial state
initial_time = 9 * 60  # 9:00 AM
initial_location = 'The Castro'

heap = [ (0, initial_time, initial_location, 0, []) ]  # (neg_num_friends, time, loc, num_friends, path)
heapq.heapify(heap)

best_so_far = {}  # (loc, time) -> max_num_friends
best_path = []
best_num_friends = 0

while heap:
    neg_num_friends, current_time, current_loc, num_friends, path = heapq.heappop(heap)
    current_num_friends = -neg_num_friends

    # Check if this state is worse than previously recorded
    key = (current_loc, current_time)
    if key in best_so_far and best_so_far[key] >= current_num_friends:
        continue
    best_so_far[key] = current_num_friends

    # Update best path if this is better
    if current_num_friends > best_num_friends:
        best_num_friends = current_num_friends
        best_path = path.copy()

    # For each friend not in the path, check if can be met
    for friend in friends:
        # Check if this friend is already in the path
        if any(meeting['friend']['name'] == friend['name'] for meeting in path):
            continue

        friend_loc = friend['location']
        friend_start = friend['available_start']
        friend_end = friend['available_end']
        required = friend['required_duration']

        # Get travel time from current_loc to friend_loc
        if current_loc not in travel_times or friend_loc not in travel_times[current_loc]:
            continue
        travel_time = travel_times[current_loc][friend_loc]

        arrival_time = current_time + travel_time

        # The earliest possible start time for the meeting is max(arrival_time, friend_start)
        # The latest possible start time is friend_end - required
        latest_start = friend_end - required
        earliest_start = max(arrival_time, friend_start)

        if earliest_start > latest_start:
            # Cannot meet this friend
            continue

        # The meeting can start at earliest_start, ends at earliest_start + required
        new_time = earliest_start + required

        # Create new path entry
        new_meeting = {
            'friend': friend,
            'start': earliest_start,
            'end': new_time
        }
        new_path = path + [new_meeting]

        new_num_friends = num_friends + 1

        # Add new state to heap
        new_key = (friend_loc, new_time)
        if new_key not in best_so_far or best_so_far[new_key] < new_num_friends:
            heapq.heappush(heap, ( -new_num_friends, new_time, friend_loc, new_num_friends, new_path ))

# Generate the itinerary from best_path
itinerary = []
for meeting in best_path:
    friend = meeting['friend']
    start_time = minutes_to_time_str(meeting['start'])
    end_time = minutes_to_time_str(meeting['end'])
    itinerary.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": start_time,
        "end_time": end_time
    })

# Output the JSON
result = {
    "itinerary": itinerary
}

print(json.dumps(result, indent=2))