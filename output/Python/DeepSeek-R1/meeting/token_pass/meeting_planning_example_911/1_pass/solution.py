import json
from collections import namedtuple

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Define the travel times dictionary
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
        'Financial District': 21
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
        'Financial District': 8
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
        'Financial District': 26
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
        'Financial District': 5
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
        'Financial District': 21
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
        'Financial District': 22
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
        'Financial District': 9
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
        'Financial District': 17
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
        'Financial District': 23
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
        'Financial District': 9
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
        'Union Square': 9
    }
}

# Define the meetings
Meeting = namedtuple('Meeting', ['name', 'location', 'start_avail', 'end_avail', 'desired_duration'])
meetings = [
    Meeting('Steven', 'North Beach', time_to_minutes('17:30'), time_to_minutes('20:30'), 15),
    Meeting('Sarah', 'Golden Gate Park', time_to_minutes('17:00'), time_to_minutes('19:15'), 75),
    Meeting('Brian', 'Embarcadero', time_to_minutes('14:15'), time_to_minutes('16:00'), 105),
    Meeting('Stephanie', 'Haight-Ashbury', time_to_minutes('10:15'), time_to_minutes('12:15'), 75),
    Meeting('Melissa', 'Richmond District', time_to_minutes('14:00'), time_to_minutes('19:30'), 30),
    Meeting('Nancy', 'Nob Hill', time_to_minutes('8:15'), time_to_minutes('12:45'), 90),
    Meeting('David', 'Marina District', time_to_minutes('11:15'), time_to_minutes('13:15'), 120),
    Meeting('James', 'Presidio', time_to_minutes('15:00'), time_to_minutes('18:15'), 120),
    Meeting('Elizabeth', 'Union Square', time_to_minutes('11:30'), time_to_minutes('21:00'), 60),
    Meeting('Robert', 'Financial District', time_to_minutes('13:15'), time_to_minutes('15:15'), 45)
]

# Dynamic programming setup
n = len(meetings)
INF = 10**9
dp = [[INF] * n for _ in range(1 << n)]
parent = [[None] * n for _ in range(1 << n)]  # Each element is (prev_mask, prev_index, start_time)

start_location = 'The Castro'
start_time_minutes = time_to_minutes('9:00')

# Initialize for meetings directly from start
for i in range(n):
    travel_time = travel_times[start_location][meetings[i].location]
    earliest_start = max(meetings[i].start_avail, start_time_minutes + travel_time)
    if earliest_start + meetings[i].desired_duration <= meetings[i].end_avail:
        dp[1 << i][i] = earliest_start + meetings[i].desired_duration
        parent[1 << i][i] = (-1, -1, earliest_start)

# Iterate over all masks
for mask in range(1 << n):
    for i in range(n):
        if dp[mask][i] == INF:
            continue
        for j in range(n):
            if mask & (1 << j):
                continue
            travel_time = travel_times[meetings[i].location][meetings[j].location]
            earliest_start = max(meetings[j].start_avail, dp[mask][i] + travel_time)
            if earliest_start + meetings[j].desired_duration <= meetings[j].end_avail:
                new_mask = mask | (1 << j)
                if earliest_start + meetings[j].desired_duration < dp[new_mask][j]:
                    dp[new_mask][j] = earliest_start + meetings[j].desired_duration
                    parent[new_mask][j] = (mask, i, earliest_start)

# Find the best solution (max number of meetings)
best_mask = 0
best_count = 0
best_finish = INF
best_j = -1
for mask in range(1 << n):
    count = bin(mask).count('1')
    for j in range(n):
        if dp[mask][j] < INF:
            if count > best_count or (count == best_count and dp[mask][j] < best_finish):
                best_count = count
                best_mask = mask
                best_finish = dp[mask][j]
                best_j = j

# Reconstruct the itinerary
itinerary = []
current_mask = best_mask
current_j = best_j
while current_j != -1:
    prev_mask, prev_j, start_time = parent[current_mask][current_j]
    meeting = meetings[current_j]
    itinerary.append({
        'action': 'meet',
        'location': meeting.location,
        'person': meeting.name,
        'start_time': minutes_to_time(start_time),
        'end_time': minutes_to_time(start_time + meeting.desired_duration)
    })
    current_mask, current_j = prev_mask, prev_j

itinerary.reverse()

# Output as JSON
output = {'itinerary': itinerary}
print(json.dumps(output, indent=2))