import json

def time_str_to_minutes(time_str):
    # Convert time string (e.g., "9:00AM" or "8:00PM") to minutes from 9:00AM
    time_str_clean = time_str.replace(" ", "")
    hour_part = time_str_clean[:-2]
    period = time_str_clean[-2:]
    hour, minute = map(int, hour_part.split(':'))
    if period == 'PM' and hour != 12:
        hour += 12
    if period == 'AM' and hour == 12:
        hour = 0
    total_minutes = hour * 60 + minute
    base_minutes = 9 * 60  # 9:00AM in minutes from midnight
    return total_minutes - base_minutes

def minutes_to_time(minutes):
    base_minutes = 9 * 60
    total_minutes = base_minutes + minutes
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h}:{m:02d}"

# Define locations
locations = [
    "Presidio",
    "Pacific Heights",
    "Golden Gate Park",
    "Fisherman's Wharf",
    "Marina District",
    "Alamo Square",
    "Sunset District",
    "Nob Hill",
    "North Beach"
]

# Build travel_times dictionary from provided data
travel_times = {
    "Presidio": {
        "Presidio": 0,
        "Pacific Heights": 11,
        "Golden Gate Park": 12,
        "Fisherman's Wharf": 19,
        "Marina District": 11,
        "Alamo Square": 19,
        "Sunset District": 15,
        "Nob Hill": 18,
        "North Beach": 18
    },
    "Pacific Heights": {
        "Presidio": 11,
        "Pacific Heights": 0,
        "Golden Gate Park": 15,
        "Fisherman's Wharf": 13,
        "Marina District": 6,
        "Alamo Square": 10,
        "Sunset District": 21,
        "Nob Hill": 8,
        "North Beach": 9
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Pacific Heights": 16,
        "Golden Gate Park": 0,
        "Fisherman's Wharf": 24,
        "Marina District": 16,
        "Alamo Square": 9,
        "Sunset District": 10,
        "Nob Hill": 20,
        "North Beach": 23
    },
    "Fisherman's Wharf": {
        "Presidio": 17,
        "Pacific Heights": 12,
        "Golden Gate Park": 25,
        "Fisherman's Wharf": 0,
        "Marina District": 9,
        "Alamo Square": 21,
        "Sunset District": 27,
        "Nob Hill": 11,
        "North Beach": 6
    },
    "Marina District": {
        "Presidio": 10,
        "Pacific Heights": 7,
        "Golden Gate Park": 18,
        "Fisherman's Wharf": 10,
        "Marina District": 0,
        "Alamo Square": 15,
        "Sunset District": 19,
        "Nob Hill": 12,
        "North Beach": 11
    },
    "Alamo Square": {
        "Presidio": 17,
        "Pacific Heights": 10,
        "Golden Gate Park": 9,
        "Fisherman's Wharf": 19,
        "Marina District": 15,
        "Alamo Square": 0,
        "Sunset District": 16,
        "Nob Hill": 11,
        "North Beach": 15
    },
    "Sunset District": {
        "Presidio": 16,
        "Pacific Heights": 21,
        "Golden Gate Park": 11,
        "Fisherman's Wharf": 29,
        "Marina District": 21,
        "Alamo Square": 17,
        "Sunset District": 0,
        "Nob Hill": 27,
        "North Beach": 28
    },
    "Nob Hill": {
        "Presidio": 17,
        "Pacific Heights": 8,
        "Golden Gate Park": 17,
        "Fisherman's Wharf": 10,
        "Marina District": 11,
        "Alamo Square": 11,
        "Sunset District": 24,
        "Nob Hill": 0,
        "North Beach": 7
    },
    "North Beach": {
        "Presidio": 17,
        "Pacific Heights": 8,
        "Golden Gate Park": 22,
        "Fisherman's Wharf": 5,
        "Marina District": 9,
        "Alamo Square": 16,
        "Sunset District": 27,
        "Nob Hill": 7,
        "North Beach": 0
    }
}

# Build travel_matrix: 9x9 matrix
travel_matrix = []
for loc1 in locations:
    row = []
    for loc2 in locations:
        row.append(travel_times[loc1][loc2])
    travel_matrix.append(row)

# Define friends and their constraints (converted to minutes from 9:00AM)
friends = [
    {'name': 'Michelle', 'location_name': 'Golden Gate Park', 'location_index': 2, 
     'start': time_str_to_minutes("8:00PM"), 'end': time_str_to_minutes("9:00PM"), 'duration': 15},
    {'name': 'Emily', 'location_name': "Fisherman's Wharf", 'location_index': 3, 
     'start': time_str_to_minutes("4:15PM"), 'end': time_str_to_minutes("7:00PM"), 'duration': 30},
    {'name': 'Mark', 'location_name': 'Marina District', 'location_index': 4, 
     'start': time_str_to_minutes("6:15PM"), 'end': time_str_to_minutes("7:45PM"), 'duration': 75},
    {'name': 'Barbara', 'location_name': 'Alamo Square', 'location_index': 5, 
     'start': time_str_to_minutes("5:00PM"), 'end': time_str_to_minutes("7:00PM"), 'duration': 120},
    {'name': 'Laura', 'location_name': 'Sunset District', 'location_index': 6, 
     'start': time_str_to_minutes("7:00PM"), 'end': time_str_to_minutes("9:15PM"), 'duration': 75},
    {'name': 'Mary', 'location_name': 'Nob Hill', 'location_index': 7, 
     'start': time_str_to_minutes("5:30PM"), 'end': time_str_to_minutes("7:00PM"), 'duration': 45},
    {'name': 'Helen', 'location_name': 'North Beach', 'location_index': 8, 
     'start': time_str_to_minutes("11:00AM"), 'end': time_str_to_minutes("12:15PM"), 'duration': 45}
]

# Map location index to friend index (if any friend is at that location)
location_to_friend = {}
for idx, friend in enumerate(friends):
    location_to_friend[friend['location_index']] = idx

# Maximum time: 9:15PM (Laura's end) -> minutes from 9:00AM
max_time = time_str_to_minutes("9:15PM")

# Initialize dp and prev arrays
dp = [[[False] * 128 for _ in range(9)] for __ in range(max_time + 1)]
prev = [[[None] * 128 for _ in range(9)] for __ in range(max_time + 1)]

# Base state: at time 0 (9:00AM) at Presidio (index 0) with no meetings
dp[0][0][0] = True

# Run the DP
for t in range(max_time + 1):
    for loc in range(9):
        for mask in range(128):
            if not dp[t][loc][mask]:
                continue
            # Option 1: Travel to another location
            for next_loc in range(9):
                if next_loc == loc:
                    continue
                tt = travel_matrix[loc][next_loc]
                nt = t + tt
                if nt <= max_time and not dp[nt][next_loc][mask]:
                    dp[nt][next_loc][mask] = True
                    prev[nt][next_loc][mask] = (t, loc, mask, 'travel', next_loc)
            # Option 2: Start a meeting at current location (if applicable)
            if loc in location_to_friend:
                friend_idx = location_to_friend[loc]
                if mask & (1 << friend_idx) == 0:
                    friend = friends[friend_idx]
                    start_meeting = max(t, friend['start'])
                    end_meeting = start_meeting + friend['duration']
                    if end_meeting <= friend['end'] and end_meeting <= max_time:
                        new_mask = mask | (1 << friend_idx)
                        if not dp[end_meeting][loc][new_mask]:
                            dp[end_meeting][loc][new_mask] = True
                            prev[end_meeting][loc][new_mask] = (t, loc, mask, 'meet', friend_idx)

# Find the state with the maximum number of meetings
best_count = -1
best_t = -1
best_loc = -1
best_mask = -1
for t in range(max_time + 1):
    for loc in range(9):
        for mask in range(128):
            if dp[t][loc][mask]:
                count = bin(mask).count("1")
                if count > best_count:
                    best_count = count
                    best_t = t
                    best_loc = loc
                    best_mask = mask

# Backtrack to get the itinerary (only meetings)
itinerary_actions = []
if best_count > 0:
    t = best_t
    loc = best_loc
    mask = best_mask
    while prev[t][loc][mask] is not None:
        prev_t, prev_loc, prev_mask, action_type, info = prev[t][loc][mask]
        if action_type == 'meet':
            friend_idx = info
            friend = friends[friend_idx]
            start_meeting = max(prev_t, friend['start'])
            end_meeting = t
            action_entry = {
                "action": "meet",
                "location": friend['location_name'],
                "person": friend['name'],
                "start_time": minutes_to_time(start_meeting),
                "end_time": minutes_to_time(end_meeting)
            }
            itinerary_actions.append(action_entry)
            t, loc, mask = prev_t, prev_loc, prev_mask
        else:
            t, loc, mask = prev_t, prev_loc, prev_mask
    itinerary_actions.reverse()

# Output the result as JSON
result = {
    "itinerary": itinerary_actions
}
print(json.dumps(result))