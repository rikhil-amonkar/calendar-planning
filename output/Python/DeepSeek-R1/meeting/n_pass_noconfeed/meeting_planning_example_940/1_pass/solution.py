import json

def time_str_to_minutes(time_str):
    if time_str.endswith("AM") or time_str.endswith("PM"):
        am_pm = time_str[-2:]
        time_part = time_str[:-2].strip()
        parts = time_part.split(':')
        if len(parts) < 2:
            hour = int(parts[0])
            minute = 0
        else:
            hour = int(parts[0])
            minute = int(parts[1])
        if am_pm == "PM" and hour != 12:
            hour += 12
        if am_pm == "AM" and hour == 12:
            hour = 0
        return hour * 60 + minute
    else:
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        return hour * 60 + minute

def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

locations = [
    "Union Square",
    "Mission District",
    "Fisherman's Wharf",
    "Russian Hill",
    "Marina District",
    "North Beach",
    "Chinatown",
    "Pacific Heights",
    "The Castro",
    "Nob Hill",
    "Sunset District"
]

travel_dict = {
    "Union Square": {
        "Mission District": 14,
        "Fisherman's Wharf": 15,
        "Russian Hill": 13,
        "Marina District": 18,
        "North Beach": 10,
        "Chinatown": 7,
        "Pacific Heights": 15,
        "The Castro": 17,
        "Nob Hill": 9,
        "Sunset District": 27
    },
    "Mission District": {
        "Union Square": 15,
        "Fisherman's Wharf": 22,
        "Russian Hill": 15,
        "Marina District": 19,
        "North Beach": 17,
        "Chinatown": 16,
        "Pacific Heights": 16,
        "The Castro": 7,
        "Nob Hill": 12,
        "Sunset District": 24
    },
    "Fisherman's Wharf": {
        "Union Square": 13,
        "Mission District": 22,
        "Russian Hill": 7,
        "Marina District": 9,
        "North Beach": 6,
        "Chinatown": 12,
        "Pacific Heights": 12,
        "The Castro": 27,
        "Nob Hill": 11,
        "Sunset District": 27
    },
    "Russian Hill": {
        "Union Square": 10,
        "Mission District": 16,
        "Fisherman's Wharf": 7,
        "Marina District": 7,
        "North Beach": 5,
        "Chinatown": 9,
        "Pacific Heights": 7,
        "The Castro": 21,
        "Nob Hill": 5,
        "Sunset District": 23
    },
    "Marina District": {
        "Union Square": 16,
        "Mission District": 20,
        "Fisherman's Wharf": 10,
        "Russian Hill": 8,
        "North Beach": 11,
        "Chinatown": 15,
        "Pacific Heights": 7,
        "The Castro": 22,
        "Nob Hill": 12,
        "Sunset District": 19
    },
    "North Beach": {
        "Union Square": 7,
        "Mission District": 18,
        "Fisherman's Wharf": 5,
        "Russian Hill": 4,
        "Marina District": 9,
        "Chinatown": 6,
        "Pacific Heights": 8,
        "The Castro": 23,
        "Nob Hill": 7,
        "Sunset District": 27
    },
    "Chinatown": {
        "Union Square": 7,
        "Mission District": 17,
        "Fisherman's Wharf": 8,
        "Russian Hill": 7,
        "Marina District": 12,
        "North Beach": 3,
        "Pacific Heights": 10,
        "The Castro": 22,
        "Nob Hill": 9,
        "Sunset District": 29
    },
    "Pacific Heights": {
        "Union Square": 12,
        "Mission District": 15,
        "Fisherman's Wharf": 13,
        "Russian Hill": 7,
        "Marina District": 6,
        "North Beach": 9,
        "Chinatown": 11,
        "The Castro": 16,
        "Nob Hill": 8,
        "Sunset District": 21
    },
    "The Castro": {
        "Union Square": 19,
        "Mission District": 7,
        "Fisherman's Wharf": 24,
        "Russian Hill": 18,
        "Marina District": 21,
        "North Beach": 20,
        "Chinatown": 22,
        "Pacific Heights": 16,
        "Nob Hill": 16,
        "Sunset District": 17
    },
    "Nob Hill": {
        "Union Square": 7,
        "Mission District": 13,
        "Fisherman's Wharf": 10,
        "Russian Hill": 5,
        "Marina District": 11,
        "North Beach": 8,
        "Chinatown": 6,
        "Pacific Heights": 8,
        "The Castro": 17,
        "Sunset District": 24
    },
    "Sunset District": {
        "Union Square": 30,
        "Mission District": 25,
        "Fisherman's Wharf": 29,
        "Russian Hill": 24,
        "Marina District": 21,
        "North Beach": 28,
        "Chinatown": 30,
        "Pacific Heights": 21,
        "The Castro": 17,
        "Nob Hill": 27
    }
}

travel_matrix = [[0]*11 for _ in range(11)]
for i in range(11):
    for j in range(11):
        if i == j:
            travel_matrix[i][j] = 0
        else:
            loc_i = locations[i]
            loc_j = locations[j]
            travel_matrix[i][j] = travel_dict[loc_i][loc_j]

friends = [
    {"name": "Kevin", "location": "Mission District", "available_start": time_str_to_minutes("8:45PM"), "available_end": time_str_to_minutes("9:45PM"), "min_duration": 60},
    {"name": "Mark", "location": "Fisherman's Wharf", "available_start": time_str_to_minutes("5:15PM"), "available_end": time_str_to_minutes("8:00PM"), "min_duration": 90},
    {"name": "Jessica", "location": "Russian Hill", "available_start": time_str_to_minutes("9:00AM"), "available_end": time_str_to_minutes("3:00PM"), "min_duration": 120},
    {"name": "Jason", "location": "Marina District", "available_start": time_str_to_minutes("3:15PM"), "available_end": time_str_to_minutes("9:45PM"), "min_duration": 120},
    {"name": "John", "location": "North Beach", "available_start": time_str_to_minutes("9:45AM"), "available_end": time_str_to_minutes("6:00PM"), "min_duration": 15},
    {"name": "Karen", "location": "Chinatown", "available_start": time_str_to_minutes("4:45PM"), "available_end": time_str_to_minutes("7:00PM"), "min_duration": 75},
    {"name": "Sarah", "location": "Pacific Heights", "available_start": time_str_to_minutes("5:30PM"), "available_end": time_str_to_minutes("6:15PM"), "min_duration": 45},
    {"name": "Amanda", "location": "The Castro", "available_start": time_str_to_minutes("8:00PM"), "available_end": time_str_to_minutes("9:15PM"), "min_duration": 60},
    {"name": "Nancy", "location": "Nob Hill", "available_start": time_str_to_minutes("9:45AM"), "available_end": time_str_to_minutes("1:00PM"), "min_duration": 45},
    {"name": "Rebecca", "location": "Sunset District", "available_start": time_str_to_minutes("8:45AM"), "available_end": time_str_to_minutes("3:00PM"), "min_duration": 75}
]

dp = {}
dp[(0,0)] = (540, None, None, None, None)

for mask in range(0, 1<<10):
    for loc in range(0, 11):
        state_key = (mask, loc)
        if state_key not in dp:
            continue
        current_end_time, parent, _, _, _ = dp[state_key]
        for i in range(0, 10):
            if mask & (1 << i):
                continue
            friend_loc_str = friends[i]['location']
            friend_loc_index = locations.index(friend_loc_str)
            travel_time = travel_matrix[loc][friend_loc_index]
            arrival_time = current_end_time + travel_time
            available_start = friends[i]['available_start']
            available_end = friends[i]['available_end']
            min_duration = friends[i]['min_duration']
            start_meeting = max(arrival_time, available_start)
            if start_meeting > available_end - min_duration:
                continue
            end_meeting = start_meeting + min_duration
            if end_meeting > available_end:
                continue
            new_mask = mask | (1 << i)
            new_loc = friend_loc_index
            new_state_key = (new_mask, new_loc)
            current_best_end = float('inf')
            if new_state_key in dp:
                current_best_end = dp[new_state_key][0]
            if end_meeting < current_best_end:
                dp[new_state_key] = (end_meeting, state_key, i, start_meeting, end_meeting)

best_state_key = None
best_count = -1
for state_key in dp:
    mask, loc = state_key
    count = bin(mask).count("1")
    if count > best_count:
        best_count = count
        best_state_key = state_key

meetings = []
current_key = best_state_key
while current_key in dp:
    state_tuple = dp[current_key]
    end_time, prev_key, friend_index, start_meeting, end_meeting = state_tuple
    if friend_index is not None:
        friend = friends[friend_index]
        meeting_entry = {
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": minutes_to_time_str(start_meeting),
            "end_time": minutes_to_time_str(end_meeting)
        }
        meetings.append(meeting_entry)
    if prev_key is None:
        break
    current_key = prev_key

meetings.reverse()
result = {
    "itinerary": meetings
}
print(json.dumps(result))