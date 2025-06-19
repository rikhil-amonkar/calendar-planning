import json

def min_to_time(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

travel_times = {
    'Union Square': {
        'Russian Hill': 13, 'Alamo Square': 15, 'Haight-Ashbury': 18, 'Marina District': 18,
        'Bayview': 15, 'Chinatown': 7, 'Presidio': 24, 'Sunset District': 27
    },
    'Russian Hill': {
        'Union Square': 10, 'Alamo Square': 15, 'Haight-Ashbury': 17, 'Marina District': 7,
        'Bayview': 23, 'Chinatown': 9, 'Presidio': 14, 'Sunset District': 23
    },
    'Alamo Square': {
        'Union Square': 14, 'Russian Hill': 13, 'Haight-Ashbury': 5, 'Marina District': 15,
        'Bayview': 16, 'Chinatown': 15, 'Presidio': 17, 'Sunset District': 16
    },
    'Haight-Ashbury': {
        'Union Square': 19, 'Russian Hill': 17, 'Alamo Square': 5, 'Marina District': 17,
        'Bayview': 18, 'Chinatown': 19, 'Presidio': 15, 'Sunset District': 15
    },
    'Marina District': {
        'Union Square': 16, 'Russian Hill': 8, 'Alamo Square': 15, 'Haight-Ashbury': 16,
        'Bayview': 27, 'Chinatown': 15, 'Presidio': 11, 'Sunset District': 19  # Updated to 11
    },
    'Bayview': {
        'Union Square': 18, 'Russian Hill': 23, 'Alamo Square': 16, 'Haight-Ashbury': 19,
        'Marina District': 27, 'Chinatown': 19, 'Presidio': 32, 'Sunset District': 23
    },
    'Chinatown': {
        'Union Square': 7, 'Russian Hill': 7, 'Alamo Square': 17, 'Haight-Ashbury': 19,
        'Marina District': 12, 'Bayview': 20, 'Presidio': 19, 'Sunset District': 29
    },
    'Presidio': {
        'Union Square': 22, 'Russian Hill': 14, 'Alamo Square': 19, 'Haight-Ashbury': 15,
        'Marina District': 11, 'Bayview': 31, 'Chinatown': 21, 'Sunset District': 16  # Updated to 11
    },
    'Sunset District': {
        'Union Square': 30, 'Russian Hill': 24, 'Alamo Square': 17, 'Haight-Ashbury': 15,
        'Marina District': 21, 'Bayview': 22, 'Chinatown': 30, 'Presidio': 16
    }
}

friends = [
    {'name': 'Betty', 'location': 'Russian Hill', 'start_avail': 420, 'end_avail': 1005, 'min_duration': 105},
    {'name': 'Melissa', 'location': 'Alamo Square', 'start_avail': 570, 'end_avail': 1035, 'min_duration': 105},
    {'name': 'Joshua', 'location': 'Haight-Ashbury', 'start_avail': 735, 'end_avail': 1140, 'min_duration': 90},
    {'name': 'Jeffrey', 'location': 'Marina District', 'start_avail': 735, 'end_avail': 1080, 'min_duration': 45},
    {'name': 'James', 'location': 'Bayview', 'start_avail': 450, 'end_avail': 1200, 'min_duration': 90},
    {'name': 'Anthony', 'location': 'Chinatown', 'start_avail': 705, 'end_avail': 810, 'min_duration': 75},
    {'name': 'Timothy', 'location': 'Presidio', 'start_avail': 750, 'end_avail': 885, 'min_duration': 90},
    {'name': 'Emily', 'location': 'Sunset District', 'start_avail': 1170, 'end_avail': 1290, 'min_duration': 120}
]

start_time = 540  # 9:00 AM in minutes
start_location = 'Union Square'
n = len(friends)
INF = 10**9
dp = [[INF] * n for _ in range(1<<n)]
parent = [[None] * n for _ in range(1<<n)]

# Initialize DP for the first meeting
for i in range(n):
    loc = friends[i]['location']
    travel = travel_times[start_location][loc]
    arrival = start_time + travel
    start_meet = max(arrival, friends[i]['start_avail'])
    end_meet = start_meet + friends[i]['min_duration']
    if end_meet <= friends[i]['end_avail']:
        dp[1<<i][i] = end_meet

# Iterate over all masks
for mask in range(1<<n):
    for i in range(n):
        if mask & (1 << i) == 0 or dp[mask][i] == INF:
            continue
        for j in range(n):
            if mask & (1 << j):
                continue
            loc_i = friends[i]['location']
            loc_j = friends[j]['location']
            travel = travel_times[loc_i][loc_j]
            arrival = dp[mask][i] + travel
            start_meet = max(arrival, friends[j]['start_avail'])
            end_meet = start_meet + friends[j]['min_duration']
            if end_meet > friends[j]['end_avail']:
                continue
            new_mask = mask | (1 << j)
            if end_meet < dp[new_mask][j]:
                dp[new_mask][j] = end_meet
                parent[new_mask][j] = (mask, i)

# Find the best itinerary (most friends, earliest finish)
best_mask = 0
best_count = -1
best_end = INF
best_j = -1
for mask in range(1<<n):
    count = bin(mask).count('1')
    for j in range(n):
        if dp[mask][j] != INF:
            if count > best_count or (count == best_count and dp[mask][j] < best_end):
                best_count = count
                best_end = dp[mask][j]
                best_mask = mask
                best_j = j

# Reconstruct itinerary
itinerary = []
if best_j != -1:
    current_mask = best_mask
    current_j = best_j
    stack = []
    while current_j is not None:
        friend = friends[current_j]
        end_time = dp[current_mask][current_j]
        start_meet = end_time - friend['min_duration']
        event = {
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": min_to_time(start_meet),
            "end_time": min_to_time(end_time)
        }
        stack.append(event)
        if parent[current_mask][current_j] is not None:
            prev_mask, prev_i = parent[current_mask][current_j]
            current_mask = prev_mask
            current_j = prev_i
        else:
            current_j = None
    itinerary = stack[::-1]

print(json.dumps({"itinerary": itinerary}))