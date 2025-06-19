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
dp = [[(10**9, -1, -1, -1, 0, 0) for _ in range(num_locations)] for _ in range(1 << n)]

dp[0][0] = (0, -1, -1, -1, 0, 0)

for mask in range(1 << n):
    for loc_idx in range(num_locations):
        current_time, _, _, _, _, _ = dp[mask][loc_idx]
        if current_time == 10**9:
            continue
        for next_friend in range(n):
            if mask & (1 << next_friend) == 0:
                next_loc_idx = friend_location_index[next_friend]
                travel_duration = travel_matrix[loc_idx][next_loc_idx]
                arrival_time = current_time + travel_duration
                friend = friends[next_friend]
                meeting_start = max(arrival_time, friend['start'])
                meeting_end = meeting_start + friend['min_duration']
                if meeting_end <= friend['end']:
                    new_mask = mask | (1 << next_friend)
                    if meeting_end < dp[new_mask][next_loc_idx][0]:
                        dp[new_mask][next_loc_idx] = (meeting_end, mask, loc_idx, next_friend, meeting_start, meeting_end)

best_mask = 0
best_count = 0
best_time = 10**9
best_loc = 0
for mask in range(1 << n):
    count = bin(mask).count("1")
    for loc_idx in range(num_locations):
        time_val = dp[mask][loc_idx][0]
        if time_val < 10**9:
            if count > best_count or (count == best_count and time_val < best_time):
                best_count = count
                best_time = time_val
                best_mask = mask
                best_loc = loc_idx

itinerary = []
mask = best_mask
loc_idx = best_loc
while mask != 0:
    state = dp[mask][loc_idx]
    meeting_end, prev_mask, prev_loc_idx, friend_idx, meeting_start, _ = state
    friend = friends[friend_idx]
    itinerary.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": convert_minutes_to_time(meeting_start),
        "end_time": convert_minutes_to_time(meeting_end)
    })
    mask = prev_mask
    loc_idx = prev_loc_idx

itinerary.reverse()
result = {"itinerary": itinerary}
print(json.dumps(result))