import json

def time_to_minutes(time_str, base_minutes=540):
    time_str = time_str.strip().upper()
    if time_str.endswith("AM") or time_str.endswith("PM"):
        t_part = time_str[:-2].strip()
        meridian = time_str[-2:]
    else:
        t_part = time_str
        meridian = None

    parts = t_part.split(':')
    hour = int(parts[0])
    minute = int(parts[1])

    if meridian:
        if meridian == "PM" and hour != 12:
            hour += 12
        elif meridian == "AM" and hour == 12:
            hour = 0

    total_minutes = hour * 60 + minute
    return total_minutes - base_minutes

def convert_minutes_to_time(minutes_relative):
    total_minutes = 540 + minutes_relative
    hour = total_minutes // 60
    minute = total_minutes % 60
    return f"{hour}:{minute:02d}"

travel_times = {
    "The Castro": {
        "Marina District": 21,
        "Presidio": 20,
        "North Beach": 20,
        "Embarcadero": 22,
        "Haight-Ashbury": 6,
        "Golden Gate Park": 11,
        "Richmond District": 16,
        "Alamo Square": 8,
        "Financial District": 21,
        "Sunset District": 17
    },
    "Marina District": {
        "The Castro": 22,
        "Presidio": 10,
        "North Beach": 11,
        "Embarcadero": 14,
        "Haight-Ashbury": 16,
        "Golden Gate Park": 18,
        "Richmond District": 11,
        "Alamo Square": 15,
        "Financial District": 17,
        "Sunset District": 19
    },
    "Presidio": {
        "The Castro": 21,
        "Marina District": 11,
        "North Beach": 18,
        "Embarcadero": 20,
        "Haight-Ashbury": 15,
        "Golden Gate Park": 12,
        "Richmond District": 7,
        "Alamo Square": 19,
        "Financial District": 23,
        "Sunset District": 15
    },
    "North Beach": {
        "The Castro": 23,
        "Marina District": 9,
        "Presidio": 17,
        "Embarcadero": 6,
        "Haight-Ashbury": 18,
        "Golden Gate Park": 22,
        "Richmond District": 18,
        "Alamo Square": 16,
        "Financial District": 8,
        "Sunset District": 27
    },
    "Embarcadero": {
        "The Castro": 25,
        "Marina District": 12,
        "Presidio": 20,
        "North Beach": 5,
        "Haight-Ashbury": 21,
        "Golden Gate Park": 25,
        "Richmond District": 21,
        "Alamo Square": 19,
        "Financial District": 5,
        "Sunset District": 30
    },
    "Haight-Ashbury": {
        "The Castro": 6,
        "Marina District": 17,
        "Presidio": 15,
        "North Beach": 19,
        "Embarcadero": 20,
        "Golden Gate Park": 7,
        "Richmond District": 10,
        "Alamo Square": 5,
        "Financial District": 21,
        "Sunset District": 15
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "Marina District": 16,
        "Presidio": 11,
        "North Beach": 23,
        "Embarcadero": 25,
        "Haight-Ashbury": 7,
        "Richmond District": 7,
        "Alamo Square": 9,
        "Financial District": 26,
        "Sunset District": 10
    },
    "Richmond District": {
        "The Castro": 16,
        "Marina District": 9,
        "Presidio": 7,
        "North Beach": 17,
        "Embarcadero": 19,
        "Haight-Ashbury": 10,
        "Golden Gate Park": 9,
        "Alamo Square": 13,
        "Financial District": 22,
        "Sunset District": 11
    },
    "Alamo Square": {
        "The Castro": 8,
        "Marina District": 15,
        "Presidio": 17,
        "North Beach": 15,
        "Embarcadero": 16,
        "Haight-Ashbury": 5,
        "Golden Gate Park": 9,
        "Richmond District": 11,
        "Financial District": 17,
        "Sunset District": 16
    },
    "Financial District": {
        "The Castro": 20,
        "Marina District": 15,
        "Presidio": 22,
        "North Beach": 7,
        "Embarcadero": 4,
        "Haight-Ashbury": 19,
        "Golden Gate Park": 23,
        "Richmond District": 21,
        "Alamo Square": 17,
        "Sunset District": 30
    },
    "Sunset District": {
        "The Castro": 17,
        "Marina District": 21,
        "Presidio": 16,
        "North Beach": 28,
        "Embarcadero": 30,
        "Haight-Ashbury": 15,
        "Golden Gate Park": 11,
        "Richmond District": 12,
        "Alamo Square": 17,
        "Financial District": 30
    }
}

location_list = [
    "The Castro",
    "Marina District",
    "Presidio",
    "North Beach",
    "Embarcadero",
    "Haight-Ashbury",
    "Golden Gate Park",
    "Richmond District",
    "Alamo Square",
    "Financial District",
    "Sunset District"
]

num_locations = len(location_list)

travel_matrix = [[0] * num_locations for _ in range(num_locations)]
for i in range(num_locations):
    from_loc = location_list[i]
    for j in range(num_locations):
        to_loc = location_list[j]
        if i == j:
            travel_matrix[i][j] = 0
        else:
            travel_matrix[i][j] = travel_times[from_loc][to_loc]

friends = [
    {'name': 'Elizabeth', 'location': 'Marina District', 
     'start': time_to_minutes("7:00PM"), 
     'end': time_to_minutes("8:45PM"), 
     'min_duration': 105},
    {'name': 'Joshua', 'location': 'Presidio', 
     'start': time_to_minutes("8:30AM"), 
     'end': time_to_minutes("1:15PM"), 
     'min_duration': 105},
    {'name': 'Timothy', 'location': 'North Beach', 
     'start': time_to_minutes("7:45PM"), 
     'end': time_to_minutes("10:00PM"), 
     'min_duration': 90},
    {'name': 'David', 'location': 'Embarcadero', 
     'start': time_to_minutes("10:45AM"), 
     'end': time_to_minutes("12:30PM"), 
     'min_duration': 30},
    {'name': 'Kimberly', 'location': 'Haight-Ashbury', 
     'start': time_to_minutes("4:45PM"), 
     'end': time_to_minutes("9:30PM"), 
     'min_duration': 75},
    {'name': 'Lisa', 'location': 'Golden Gate Park', 
     'start': time_to_minutes("5:30PM"), 
     'end': time_to_minutes("9:45PM"), 
     'min_duration': 45},
    {'name': 'Ronald', 'location': 'Richmond District', 
     'start': time_to_minutes("8:00AM"), 
     'end': time_to_minutes("9:30AM"), 
     'min_duration': 90},
    {'name': 'Stephanie', 'location': 'Alamo Square', 
     'start': time_to_minutes("3:30PM"), 
     'end': time_to_minutes("4:30PM"), 
     'min_duration': 30},
    {'name': 'Helen', 'location': 'Financial District', 
     'start': time_to_minutes("5:30PM"), 
     'end': time_to_minutes("6:30PM"), 
     'min_duration': 45},
    {'name': 'Laura', 'location': 'Sunset District', 
     'start': time_to_minutes("5:45PM"), 
     'end': time_to_minutes("9:15PM"), 
     'min_duration': 90}
]

friend_location_index = []
for friend in friends:
    loc = friend['location']
    friend_location_index.append(location_list.index(loc))

n = len(friends)
INF = 10**9
# DP state: dp[mask][loc] = (current_time, total_time, prev_mask, prev_loc, friend_index, meeting_start, meeting_end)
dp = [[(INF, INF, -1, -1, -1, 0, 0) for _ in range(num_locations)] for _ in range(1 << n)]

# Start at The Castro (index 0) at time 0 (9:00 AM)
dp[0][0] = (0, 0, -1, -1, -1, 0, 0)

for mask in range(1 << n):
    for loc in range(num_locations):
        current_time, total_time, _, _, _, _, _ = dp[mask][loc]
        if current_time == INF:
            continue
        for next_friend in range(n):
            if mask & (1 << next_friend):
                continue
            next_loc = friend_location_index[next_friend]
            travel_duration = travel_matrix[loc][next_loc]
            arrival_time = current_time + travel_duration
            friend = friends[next_friend]
            # Calculate meeting start time (can't be earlier than friend's available start)
            meeting_start = max(arrival_time, friend['start'])
            meeting_end = meeting_start + friend['min_duration']
            # Check if meeting fits in friend's window
            if meeting_end > friend['end']:
                continue
            # Update state after meeting
            new_time = meeting_end
            new_total = total_time + travel_duration + friend['min_duration']
            new_mask = mask | (1 << next_friend)
            # Update DP state if we found a better way
            if new_time < dp[new_mask][next_loc][0] or (new_time == dp[new_mask][next_loc][0] and new_total < dp[new_mask][next_loc][1]):
                dp[new_mask][next_loc] = (new_time, new_total, mask, loc, next_friend, meeting_start, meeting_end)

# Find best solution that returns to The Castro by 9:00 PM (780 minutes)
best_count = -1
best_total_time = INF
best_mask = -1
best_loc = -1
for mask in range(1 << n):
    count = bin(mask).count("1")
    for loc in range(num_locations):
        current_time, total_time, _, _, _, _, _ = dp[mask][loc]
        if current_time == INF:
            continue
        return_time = current_time + travel_matrix[loc][0]
        if return_time > 780:  # 9:00 PM is 780 minutes from 9:00 AM
            continue
        total_time_with_return = total_time + travel_matrix[loc][0]
        if count > best_count or (count == best_count and total_time_with_return < best_total_time):
            best_count = count
            best_total_time = total_time_with_return
            best_mask = mask
            best_loc = loc

# Reconstruct itinerary
itinerary = []
mask = best_mask
loc = best_loc
while mask != 0:
    state = dp[mask][loc]
    _, _, prev_mask, prev_loc, friend_idx, meeting_start, meeting_end = state
    friend = friends[friend_idx]
    itinerary.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": convert_minutes_to_time(meeting_start),
        "end_time": convert_minutes_to_time(meeting_end)
    })
    mask = prev_mask
    loc = prev_loc

itinerary.reverse()
result = {"itinerary": itinerary}
print(json.dumps(result))