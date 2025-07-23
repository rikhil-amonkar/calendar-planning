import json

def min_to_time(m):
    total_minutes = 540 + m
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

travel_times = {
    'The Castro': {
        'Marina District': 21,
        'Presidio': 20,
        'North Beach': 20,
        'Embarcadero': 22,
        'Haight-Ashbury': 6,
        'Golden Gate Park': 11,
        'Richmond District': 16,
        'Alamo Square': 8,
        'Financial District': 21,
        'Sunset District': 17
    },
    'Marina District': {
        'The Castro': 22,
        'Presidio': 10,
        'North Beach': 11,
        'Embarcadero': 14,
        'Haight-Ashbury': 16,
        'Golden Gate Park': 18,
        'Richmond District': 11,
        'Alamo Square': 15,
        'Financial District': 17,
        'Sunset District': 19
    },
    'Presidio': {
        'The Castro': 21,
        'Marina District': 11,
        'North Beach': 18,
        'Embarcadero': 20,
        'Haight-Ashbury': 15,
        'Golden Gate Park': 12,
        'Richmond District': 7,
        'Alamo Square': 19,
        'Financial District': 23,
        'Sunset District': 15
    },
    'North Beach': {
        'The Castro': 23,
        'Marina District': 9,
        'Presidio': 17,
        'Embarcadero': 6,
        'Haight-Ashbury': 18,
        'Golden Gate Park': 22,
        'Richmond District': 18,
        'Alamo Square': 16,
        'Financial District': 8,
        'Sunset District': 27
    },
    'Embarcadero': {
        'The Castro': 25,
        'Marina District': 12,
        'Presidio': 20,
        'North Beach': 5,
        'Haight-Ashbury': 21,
        'Golden Gate Park': 25,
        'Richmond District': 21,
        'Alamo Square': 19,
        'Financial District': 5,
        'Sunset District': 30
    },
    'Haight-Ashbury': {
        'The Castro': 6,
        'Marina District': 17,
        'Presidio': 15,
        'North Beach': 19,
        'Embarcadero': 20,
        'Golden Gate Park': 7,
        'Richmond District': 10,
        'Alamo Square': 5,
        'Financial District': 21,
        'Sunset District': 15
    },
    'Golden Gate Park': {
        'The Castro': 13,
        'Marina District': 16,
        'Presidio': 11,
        'North Beach': 23,
        'Embarcadero': 25,
        'Haight-Ashbury': 7,
        'Richmond District': 7,
        'Alamo Square': 9,
        'Financial District': 26,
        'Sunset District': 10
    },
    'Richmond District': {
        'The Castro': 16,
        'Marina District': 9,
        'Presidio': 7,
        'North Beach': 17,
        'Embarcadero': 19,
        'Haight-Ashbury': 10,
        'Golden Gate Park': 9,
        'Alamo Square': 13,
        'Financial District': 22,
        'Sunset District': 11
    },
    'Alamo Square': {
        'The Castro': 8,
        'Marina District': 15,
        'Presidio': 17,
        'North Beach': 15,
        'Embarcadero': 16,
        'Haight-Ashbury': 5,
        'Golden Gate Park': 9,
        'Richmond District': 11,
        'Financial District': 17,
        'Sunset District': 16
    },
    'Financial District': {
        'The Castro': 20,
        'Marina District': 15,
        'Presidio': 22,
        'North Beach': 7,
        'Embarcadero': 4,
        'Haight-Ashbury': 19,
        'Golden Gate Park': 23,
        'Richmond District': 21,
        'Alamo Square': 17,
        'Sunset District': 30
    },
    'Sunset District': {
        'The Castro': 17,
        'Marina District': 21,
        'Presidio': 16,
        'North Beach': 28,
        'Embarcadero': 30,
        'Haight-Ashbury': 15,
        'Golden Gate Park': 11,
        'Richmond District': 12,
        'Alamo Square': 17,
        'Financial District': 30
    }
}

friends = [
    {'name': 'Joshua', 'location': 'Presidio', 'start': -30, 'end': 255, 'duration': 105},
    {'name': 'David', 'location': 'Embarcadero', 'start': 105, 'end': 210, 'duration': 30},
    {'name': 'Stephanie', 'location': 'Alamo Square', 'start': 390, 'end': 450, 'duration': 30},
    {'name': 'Kimberly', 'location': 'Haight-Ashbury', 'start': 465, 'end': 750, 'duration': 75},
    {'name': 'Lisa', 'location': 'Golden Gate Park', 'start': 510, 'end': 765, 'duration': 45},
    {'name': 'Helen', 'location': 'Financial District', 'start': 510, 'end': 570, 'duration': 45},
    {'name': 'Laura', 'location': 'Sunset District', 'start': 525, 'end': 735, 'duration': 90},
    {'name': 'Elizabeth', 'location': 'Marina District', 'start': 600, 'end': 705, 'duration': 105},
    {'name': 'Timothy', 'location': 'North Beach', 'start': 645, 'end': 780, 'duration': 90}
]

n = len(friends)
dp = [[10**9] * n for _ in range(1 << n)]
parent = [[(-1, -1) for _ in range(n)] for _ in range(1 << n)]

for j in range(n):
    loc_j = friends[j]['location']
    travel_time = travel_times['The Castro'][loc_j]
    arrive_time = travel_time
    start_time = max(arrive_time, friends[j]['start'])
    end_time = start_time + friends[j]['duration']
    if end_time <= friends[j]['end']:
        mask_j = 1 << j
        dp[mask_j][j] = end_time
        parent[mask_j][j] = (0, -1)

for mask in range(1 << n):
    for j in range(n):
        if dp[mask][j] == 10**9:
            continue
        for k in range(n):
            if mask & (1 << k):
                continue
            loc_j = friends[j]['location']
            loc_k = friends[k]['location']
            travel_time = travel_times[loc_j][loc_k]
            arrive_time = dp[mask][j] + travel_time
            start_time = max(arrive_time, friends[k]['start'])
            end_time = start_time + friends[k]['duration']
            if end_time <= friends[k]['end']:
                new_mask = mask | (1 << k)
                if end_time < dp[new_mask][k]:
                    dp[new_mask][k] = end_time
                    parent[new_mask][k] = (mask, j)

best_count = -1
best_mask = -1
best_j = -1
for mask in range(1 << n):
    for j in range(n):
        if dp[mask][j] == 10**9:
            continue
        count = bin(mask).count('1')
        if count > best_count:
            best_count = count
            best_mask = mask
            best_j = j

itinerary_events = []
if best_count > 0:
    current_mask = best_mask
    current_j = best_j
    stack = []
    while current_mask != 0:
        end_time_val = dp[current_mask][current_j]
        start_time_val = end_time_val - friends[current_j]['duration']
        event = {
            'action': 'meet',
            'location': friends[current_j]['location'],
            'person': friends[current_j]['name'],
            'start_time': min_to_time(start_time_val),
            'end_time': min_to_time(end_time_val)
        }
        stack.append(event)
        prev_mask, prev_j = parent[current_mask][current_j]
        current_mask = prev_mask
        current_j = prev_j
    itinerary_events = stack[::-1]

result = {
    "itinerary": itinerary_events
}
print(json.dumps(result))