import json

def parse_time(time_str):
    if time_str.endswith("AM") or time_str.endswith("PM"):
        parts = time_str.split(':')
        hour_part = parts[0]
        rest = parts[1]
        minute_part = rest[:2]
        ampm = rest[2:].strip()
        hour = int(hour_part)
        minute = int(minute_part)
        if ampm == 'PM' and hour != 12:
            hour += 12
        if ampm == 'AM' and hour == 12:
            hour = 0
        total_minutes_since_midnight = hour * 60 + minute
        return total_minutes_since_midnight - 540
    else:
        raise ValueError(f"Invalid time string: {time_str}")

def minutes_to_time(minutes_since_900):
    total_minutes_since_midnight = minutes_since_900 + 540
    hour = total_minutes_since_midnight // 60
    minute = total_minutes_since_midnight % 60
    return f"{hour}:{minute:02d}"

travel_times = {
    "Richmond District": {
        "Richmond District": 0, "The Castro": 16, "Nob Hill": 17, "Marina District": 9,
        "Pacific Heights": 10, "Haight-Ashbury": 10, "Mission District": 20, "Chinatown": 20,
        "Russian Hill": 13, "Alamo Square": 13, "Bayview": 27
    },
    "The Castro": {
        "Richmond District": 16, "The Castro": 0, "Nob Hill": 16, "Marina District": 21,
        "Pacific Heights": 16, "Haight-Ashbury": 6, "Mission District": 7, "Chinatown": 22,
        "Russian Hill": 18, "Alamo Square": 8, "Bayview": 19
    },
    "Nob Hill": {
        "Richmond District": 14, "The Castro": 17, "Nob Hill": 0, "Marina District": 11,
        "Pacific Heights": 8, "Haight-Ashbury": 13, "Mission District": 13, "Chinatown": 6,
        "Russian Hill": 5, "Alamo Square": 11, "Bayview": 19
    },
    "Marina District": {
        "Richmond District": 11, "The Castro": 22, "Nob Hill": 12, "Marina District": 0,
        "Pacific Heights": 7, "Haight-Ashbury": 16, "Mission District": 20, "Chinatown": 15,
        "Russian Hill": 8, "Alamo Square": 15, "Bayview": 27
    },
    "Pacific Heights": {
        "Richmond District": 12, "The Castro": 16, "Nob Hill": 8, "Marina District": 6,
        "Pacific Heights": 0, "Haight-Ashbury": 11, "Mission District": 15, "Chinatown": 11,
        "Russian Hill": 7, "Alamo Square": 10, "Bayview": 22
    },
    "Haight-Ashbury": {
        "Richmond District": 10, "The Castro": 6, "Nob Hill": 15, "Marina District": 17,
        "Pacific Heights": 12, "Haight-Ashbury": 0, "Mission District": 11, "Chinatown": 19,
        "Russian Hill": 17, "Alamo Square": 5, "Bayview": 18
    },
    "Mission District": {
        "Richmond District": 20, "The Castro": 7, "Nob Hill": 12, "Marina District": 19,
        "Pacific Heights": 16, "Haight-Ashbury": 12, "Mission District": 0, "Chinatown": 16,
        "Russian Hill": 15, "Alamo Square": 11, "Bayview": 14
    },
    "Chinatown": {
        "Richmond District": 20, "The Castro": 22, "Nob Hill": 9, "Marina District": 12,
        "Pacific Heights": 10, "Haight-Ashbury": 19, "Mission District": 17, "Chinatown": 0,
        "Russian Hill": 7, "Alamo Square": 17, "Bayview": 20
    },
    "Russian Hill": {
        "Richmond District": 14, "The Castro": 21, "Nob Hill": 5, "Marina District": 7,
        "Pacific Heights": 7, "Haight-Ashbury": 17, "Mission District": 16, "Chinatown": 9,
        "Russian Hill": 0, "Alamo Square": 15, "Bayview": 23
    },
    "Alamo Square": {
        "Richmond District": 11, "The Castro": 8, "Nob Hill": 11, "Marina District": 15,
        "Pacific Heights": 10, "Haight-Ashbury": 5, "Mission District": 10, "Chinatown": 15,
        "Russian Hill": 13, "Alamo Square": 0, "Bayview": 16
    },
    "Bayview": {
        "Richmond District": 25, "The Castro": 19, "Nob Hill": 20, "Marina District": 27,
        "Pacific Heights": 23, "Haight-Ashbury": 19, "Mission District": 13, "Chinatown": 19,
        "Russian Hill": 23, "Alamo Square": 16, "Bayview": 0
    }
}

friends = [
    {'name': 'Matthew', 'location': 'The Castro', 
     'start': parse_time('4:30PM'), 'end': parse_time('8:00PM'), 'min_duration': 45},
    {'name': 'Rebecca', 'location': 'Nob Hill', 
     'start': parse_time('3:15PM'), 'end': parse_time('7:15PM'), 'min_duration': 105},
    {'name': 'Brian', 'location': 'Marina District', 
     'start': parse_time('2:15PM'), 'end': parse_time('10:00PM'), 'min_duration': 30},
    {'name': 'Emily', 'location': 'Pacific Heights', 
     'start': parse_time('11:15AM'), 'end': parse_time('7:45PM'), 'min_duration': 15},
    {'name': 'Karen', 'location': 'Haight-Ashbury', 
     'start': parse_time('11:45AM'), 'end': parse_time('5:30PM'), 'min_duration': 30},
    {'name': 'Stephanie', 'location': 'Mission District', 
     'start': parse_time('1:00PM'), 'end': parse_time('3:45PM'), 'min_duration': 75},
    {'name': 'James', 'location': 'Chinatown', 
     'start': parse_time('2:30PM'), 'end': parse_time('7:00PM'), 'min_duration': 120},
    {'name': 'Steven', 'location': 'Russian Hill', 
     'start': parse_time('2:00PM'), 'end': parse_time('8:00PM'), 'min_duration': 30},
    {'name': 'Elizabeth', 'location': 'Alamo Square', 
     'start': parse_time('1:00PM'), 'end': parse_time('5:15PM'), 'min_duration': 120},
    {'name': 'William', 'location': 'Bayview', 
     'start': parse_time('6:15PM'), 'end': parse_time('8:15PM'), 'min_duration': 90}
]

n = len(friends)
dp = [[None] * n for _ in range(1<<n)]

for i in range(n):
    loc = friends[i]['location']
    travel_time = travel_times['Richmond District'][loc]
    arrive = travel_time
    start = max(arrive, friends[i]['start'])
    end = start + friends[i]['min_duration']
    if end <= friends[i]['end']:
        mask = 1 << i
        dp[mask][i] = (end, -1, start, end)

for mask in range(1<<n):
    for i in range(n):
        if not (mask & (1<<i)):
            continue
        if dp[mask][i] is None:
            continue
        current_finish = dp[mask][i][0]
        current_loc = friends[i]['location']
        for j in range(n):
            if mask & (1<<j):
                continue
            next_loc = friends[j]['location']
            tt = travel_times[current_loc][next_loc]
            arrive = current_finish + tt
            start_j = max(arrive, friends[j]['start'])
            end_j = start_j + friends[j]['min_duration']
            if end_j > friends[j]['end']:
                continue
            new_mask = mask | (1<<j)
            current_state = dp[new_mask][j]
            if current_state is None or end_j < current_state[0]:
                dp[new_mask][j] = (end_j, i, start_j, end_j)

best_mask = None
best_count = -1
best_finish = None
best_j = None
for mask in range(1<<n):
    count = bin(mask).count('1')
    if count < best_count:
        continue
    for j in range(n):
        if dp[mask][j] is not None:
            if count > best_count or (count == best_count and (best_finish is None or dp[mask][j][0] < best_finish)):
                best_count = count
                best_mask = mask
                best_j = j
                best_finish = dp[mask][j][0]

if best_count == 0:
    itinerary = []
else:
    reverse_itinerary = []
    current_mask = best_mask
    current_j = best_j
    while current_j != -1:
        state = dp[current_mask][current_j]
        meeting = {
            "action": "meet",
            "location": friends[current_j]['location'],
            "person": friends[current_j]['name'],
            "start_time": minutes_to_time(state[2]),
            "end_time": minutes_to_time(state[3])
        }
        reverse_itinerary.append(meeting)
        prev_i = state[1]
        current_mask = current_mask & ~(1<<current_j)
        current_j = prev_i
    itinerary = reverse_itinerary[::-1]

result = {
    "itinerary": itinerary
}
print(json.dumps(result))