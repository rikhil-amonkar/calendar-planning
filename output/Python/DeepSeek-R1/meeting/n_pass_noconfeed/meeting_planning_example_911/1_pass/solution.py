import json

def time_to_min(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1]) if len(parts) > 1 else 0
    return hour * 60 + minute

def min_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Define travel times dictionary
travel_dict = {
    "The Castro": {
        "North Beach": 20,
        "Golden Gate Park": 11,
        "Embarcadero": 22,
        "Haight-Ashbury": 6,
        "Richmond District": 16,
        "Nob Hill": 16,
        "Marina District": 21,
        "Presidio": 20,
        "Union Square": 19,
        "Financial District": 21
    },
    "North Beach": {
        "The Castro": 23,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Haight-Ashbury": 18,
        "Richmond District": 18,
        "Nob Hill": 7,
        "Marina District": 9,
        "Presidio": 17,
        "Union Square": 7,
        "Financial District": 8
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "North Beach": 23,
        "Embarcadero": 25,
        "Haight-Ashbury": 7,
        "Richmond District": 7,
        "Nob Hill": 20,
        "Marina District": 16,
        "Presidio": 11,
        "Union Square": 22,
        "Financial District": 26
    },
    "Embarcadero": {
        "The Castro": 25,
        "North Beach": 5,
        "Golden Gate Park": 25,
        "Haight-Ashbury": 21,
        "Richmond District": 21,
        "Nob Hill": 10,
        "Marina District": 12,
        "Presidio": 20,
        "Union Square": 10,
        "Financial District": 5
    },
    "Haight-Ashbury": {
        "The Castro": 6,
        "North Beach": 19,
        "Golden Gate Park": 7,
        "Embarcadero": 20,
        "Richmond District": 10,
        "Nob Hill": 15,
        "Marina District": 17,
        "Presidio": 15,
        "Union Square": 19,
        "Financial District": 21
    },
    "Richmond District": {
        "The Castro": 16,
        "North Beach": 17,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Haight-Ashbury": 10,
        "Nob Hill": 17,
        "Marina District": 9,
        "Presidio": 7,
        "Union Square": 21,
        "Financial District": 22
    },
    "Nob Hill": {
        "The Castro": 17,
        "North Beach": 8,
        "Golden Gate Park": 17,
        "Embarcadero": 9,
        "Haight-Ashbury": 13,
        "Richmond District": 14,
        "Marina District": 11,
        "Presidio": 17,
        "Union Square": 7,
        "Financial District": 9
    },
    "Marina District": {
        "The Castro": 22,
        "North Beach": 11,
        "Golden Gate Park": 18,
        "Embarcadero": 14,
        "Haight-Ashbury": 16,
        "Richmond District": 11,
        "Nob Hill": 12,
        "Presidio": 10,
        "Union Square": 16,
        "Financial District": 17
    },
    "Presidio": {
        "The Castro": 21,
        "North Beach": 18,
        "Golden Gate Park": 12,
        "Embarcadero": 20,
        "Haight-Ashbury": 15,
        "Richmond District": 7,
        "Nob Hill": 18,
        "Marina District": 11,
        "Union Square": 22,
        "Financial District": 23
    },
    "Union Square": {
        "The Castro": 17,
        "North Beach": 10,
        "Golden Gate Park": 22,
        "Embarcadero": 11,
        "Haight-Ashbury": 18,
        "Richmond District": 20,
        "Nob Hill": 9,
        "Marina District": 18,
        "Presidio": 24,
        "Financial District": 9
    },
    "Financial District": {
        "The Castro": 20,
        "North Beach": 7,
        "Golden Gate Park": 23,
        "Embarcadero": 4,
        "Haight-Ashbury": 19,
        "Richmond District": 21,
        "Nob Hill": 8,
        "Marina District": 15,
        "Presidio": 22,
        "Union Square": 9
    }
}

# List of locations
location_list = [
    "The Castro",
    "North Beach",
    "Golden Gate Park",
    "Embarcadero",
    "Haight-Ashbury",
    "Richmond District",
    "Nob Hill",
    "Marina District",
    "Presidio",
    "Union Square",
    "Financial District"
]

# Build travel matrix
n_locations = len(location_list)
travel_matrix = [[0] * n_locations for _ in range(n_locations)]

for i, loc1 in enumerate(location_list):
    for j, loc2 in enumerate(location_list):
        if loc1 == loc2:
            travel_matrix[i][j] = 0
        else:
            travel_matrix[i][j] = travel_dict[loc1].get(loc2, 10**9)

# Define friends with their constraints
friends = [
    {'name': 'Steven', 'location': 'North Beach', 'start': time_to_min('17:30'), 'end': time_to_min('20:30'), 'min_duration': 15},
    {'name': 'Sarah', 'location': 'Golden Gate Park', 'start': time_to_min('17:00'), 'end': time_to_min('19:15'), 'min_duration': 75},
    {'name': 'Brian', 'location': 'Embarcadero', 'start': time_to_min('14:15'), 'end': time_to_min('16:00'), 'min_duration': 105},
    {'name': 'Stephanie', 'location': 'Haight-Ashbury', 'start': time_to_min('10:15'), 'end': time_to_min('12:15'), 'min_duration': 75},
    {'name': 'Melissa', 'location': 'Richmond District', 'start': time_to_min('14:00'), 'end': time_to_min('19:30'), 'min_duration': 30},
    {'name': 'Nancy', 'location': 'Nob Hill', 'start': time_to_min('8:15'), 'end': time_to_min('12:45'), 'min_duration': 90},
    {'name': 'David', 'location': 'Marina District', 'start': time_to_min('11:15'), 'end': time_to_min('13:15'), 'min_duration': 120},
    {'name': 'James', 'location': 'Presidio', 'start': time_to_min('15:00'), 'end': time_to_min('18:15'), 'min_duration': 120},
    {'name': 'Elizabeth', 'location': 'Union Square', 'start': time_to_min('11:30'), 'end': time_to_min('21:00'), 'min_duration': 60},
    {'name': 'Robert', 'location': 'Financial District', 'start': time_to_min('13:15'), 'end': time_to_min('15:15'), 'min_duration': 45}
]

# Map friend index to location index
friend_index_to_location_index = []
for friend in friends:
    loc_name = friend['location']
    idx = location_list.index(loc_name)
    friend_index_to_location_index.append(idx)

n_friends = len(friends)
n_masks = 1 << n_friends

# Initialize DP and parent arrays
dp = [[10**9] * n_friends for _ in range(n_masks)]
parent = [[None] * n_friends for _ in range(n_masks)]  # Each will store (prev_mask, prev_friend, start_time, end_time)

# Start at The Castro (index 0) at 9:00 AM (540 minutes)
start_time_global = 540  # 9:00 AM

# Initialize for each friend: travel from The Castro to the friend's location
for i in range(n_friends):
    loc_idx = friend_index_to_location_index[i]
    travel_time = travel_matrix[0][loc_idx]  # from The Castro (0) to friend's location
    arrival = start_time_global + travel_time
    start_meeting = max(arrival, friends[i]['start'])
    end_meeting = start_meeting + friends[i]['min_duration']
    if end_meeting <= friends[i]['end']:
        mask = 1 << i
        dp[mask][i] = end_meeting
        parent[mask][i] = (-1, -1, start_meeting, end_meeting)  # -1 indicates coming from start

# DP: iterate over all masks
for mask in range(n_masks):
    for i in range(n_friends):
        if dp[mask][i] == 10**9:
            continue
        for j in range(n_friends):
            if mask & (1 << j):
                continue
            loc_i = friend_index_to_location_index[i]
            loc_j = friend_index_to_location_index[j]
            travel_time = travel_matrix[loc_i][loc_j]
            arrival = dp[mask][i] + travel_time
            start_meeting = max(arrival, friends[j]['start'])
            end_meeting = start_meeting + friends[j]['min_duration']
            if end_meeting > friends[j]['end']:
                continue
            new_mask = mask | (1 << j)
            if end_meeting < dp[new_mask][j]:
                dp[new_mask][j] = end_meeting
                parent[new_mask][j] = (mask, i, start_meeting, end_meeting)

# Find the best state: maximum number of meetings, and then minimal end time
best_count = 0
best_mask = 0
best_j = -1
best_end = 10**9

for mask in range(n_masks):
    for j in range(n_friends):
        if dp[mask][j] == 10**9:
            continue
        count = bin(mask).count("1")
        if count > best_count or (count == best_count and dp[mask][j] < best_end):
            best_count = count
            best_mask = mask
            best_j = j
            best_end = dp[mask][j]

# Reconstruct the itinerary
itinerary = []
current_mask = best_mask
current_j = best_j

while current_j != -1:
    if parent[current_mask][current_j] is None:
        break
    prev_mask, prev_i, start_time, end_time = parent[current_mask][current_j]
    friend = friends[current_j]
    itinerary.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": min_to_time(start_time),
        "end_time": min_to_time(end_time)
    })
    current_mask = prev_mask
    current_j = prev_i

# Reverse to get chronological order
itinerary.reverse()

# Output as JSON
result = {
    "itinerary": itinerary
}
print(json.dumps(result))