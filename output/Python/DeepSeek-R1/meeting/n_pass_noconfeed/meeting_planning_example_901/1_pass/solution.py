import json
from collections import deque

def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

# Define travel_times dictionary
travel_times = {
    "Russian Hill": {
        "Pacific Heights": 7,
        "North Beach": 5,
        "Golden Gate Park": 21,
        "Embarcadero": 8,
        "Haight-Ashbury": 17,
        "Fisherman's Wharf": 7,
        "Mission District": 16,
        "Alamo Square": 15,
        "Bayview": 23,
        "Richmond District": 14
    },
    "Pacific Heights": {
        "Russian Hill": 7,
        "North Beach": 9,
        "Golden Gate Park": 15,
        "Embarcadero": 10,
        "Haight-Ashbury": 11,
        "Fisherman's Wharf": 13,
        "Mission District": 15,
        "Alamo Square": 10,
        "Bayview": 22,
        "Richmond District": 12
    },
    "North Beach": {
        "Russian Hill": 4,
        "Pacific Heights": 8,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Haight-Ashbury": 18,
        "Fisherman's Wharf": 5,
        "Mission District": 18,
        "Alamo Square": 16,
        "Bayview": 25,
        "Richmond District": 18
    },
    "Golden Gate Park": {
        "Russian Hill": 19,
        "Pacific Heights": 16,
        "North Beach": 23,
        "Embarcadero": 25,
        "Haight-Ashbury": 7,
        "Fisherman's Wharf": 24,
        "Mission District": 17,
        "Alamo Square": 9,
        "Bayview": 23,
        "Richmond District": 7
    },
    "Embarcadero": {
        "Russian Hill": 8,
        "Pacific Heights": 11,
        "North Beach": 5,
        "Golden Gate Park": 25,
        "Haight-Ashbury": 21,
        "Fisherman's Wharf": 6,
        "Mission District": 20,
        "Alamo Square": 19,
        "Bayview": 21,
        "Richmond District": 21
    },
    "Haight-Ashbury": {
        "Russian Hill": 17,
        "Pacific Heights": 12,
        "North Beach": 19,
        "Golden Gate Park": 7,
        "Embarcadero": 20,
        "Fisherman's Wharf": 23,
        "Mission District": 11,
        "Alamo Square": 5,
        "Bayview": 18,
        "Richmond District": 10
    },
    "Fisherman's Wharf": {
        "Russian Hill": 7,
        "Pacific Heights": 12,
        "North Beach": 6,
        "Golden Gate Park": 25,
        "Embarcadero": 8,
        "Haight-Ashbury": 22,
        "Mission District": 22,
        "Alamo Square": 21,
        "Bayview": 26,
        "Richmond District": 18
    },
    "Mission District": {
        "Russian Hill": 15,
        "Pacific Heights": 16,
        "North Beach": 17,
        "Golden Gate Park": 17,
        "Embarcadero": 19,
        "Haight-Ashbury": 12,
        "Fisherman's Wharf": 22,
        "Alamo Square": 11,
        "Bayview": 14,
        "Richmond District": 20
    },
    "Alamo Square": {
        "Russian Hill": 13,
        "Pacific Heights": 10,
        "North Beach": 15,
        "Golden Gate Park": 9,
        "Embarcadero": 16,
        "Haight-Ashbury": 5,
        "Fisherman's Wharf": 19,
        "Mission District": 10,
        "Bayview": 16,
        "Richmond District": 11
    },
    "Bayview": {
        "Russian Hill": 23,
        "Pacific Heights": 23,
        "North Beach": 22,
        "Golden Gate Park": 22,
        "Embarcadero": 19,
        "Haight-Ashbury": 19,
        "Fisherman's Wharf": 25,
        "Mission District": 13,
        "Alamo Square": 16,
        "Richmond District": 25
    },
    "Richmond District": {
        "Russian Hill": 13,
        "Pacific Heights": 10,
        "North Beach": 17,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Haight-Ashbury": 10,
        "Fisherman's Wharf": 18,
        "Mission District": 20,
        "Alamo Square": 13,
        "Bayview": 27
    }
}

# Define friends list with time in minutes
friends = [
    {"name": "Emily", "location": "Pacific Heights", "start": 555, "end": 825, "min_duration": 120},
    {"name": "Helen", "location": "North Beach", "start": 825, "end": 1125, "min_duration": 30},
    {"name": "Kimberly", "location": "Golden Gate Park", "start": 1125, "end": 1275, "min_duration": 75},
    {"name": "James", "location": "Embarcadero", "start": 630, "end": 690, "min_duration": 30},
    {"name": "Linda", "location": "Haight-Ashbury", "start": 450, "end": 1155, "min_duration": 15},
    {"name": "Paul", "location": "Fisherman's Wharf", "start": 885, "end": 1125, "min_duration": 90},
    {"name": "Anthony", "location": "Mission District", "start": 480, "end": 885, "min_duration": 105},
    {"name": "Nancy", "location": "Alamo Square", "start": 510, "end": 825, "min_duration": 120},
    {"name": "William", "location": "Bayview", "start": 1050, "end": 1230, "min_duration": 120},
    {"name": "Margaret", "location": "Richmond District", "start": 915, "end": 1095, "min_duration": 45}
]

n = len(friends)
dp = {}
parent = {}
queue = deque()

# Initialize DP with meetings from Russian Hill
for i in range(n):
    loc = friends[i]['location']
    travel_time = travel_times["Russian Hill"][loc]
    arrival = 540 + travel_time
    start_meeting = max(arrival, friends[i]['start'])
    end_meeting = start_meeting + friends[i]['min_duration']
    if end_meeting <= friends[i]['end']:
        mask = 1 << i
        dp[(mask, i)] = end_meeting
        parent[(mask, i)] = (None, None)
        queue.append((mask, i))

# BFS to explore all states
while queue:
    mask, i = queue.popleft()
    current_end = dp[(mask, i)]
    current_loc = friends[i]['location']
    for j in range(n):
        if mask & (1 << j):
            continue
        next_loc = friends[j]['location']
        travel_time_val = travel_times[current_loc][next_loc]
        arrival = current_end + travel_time_val
        start_meeting = max(arrival, friends[j]['start'])
        end_meeting = start_meeting + friends[j]['min_duration']
        if end_meeting > friends[j]['end']:
            continue
        new_mask = mask | (1 << j)
        if (new_mask, j) not in dp or dp[(new_mask, j)] > end_meeting:
            dp[(new_mask, j)] = end_meeting
            parent[(new_mask, j)] = (mask, i)
            queue.append((new_mask, j))

# Find state with maximum number of meetings
best_state = None
max_meetings = 0
for (mask, i), end_time in dp.items():
    count = bin(mask).count("1")
    if count > max_meetings:
        max_meetings = count
        best_state = (mask, i)

# Reconstruct the itinerary
itinerary = []
if best_state is not None:
    state = best_state
    while state in parent and parent[state] != (None, None):
        mask, i = state
        end_time = dp[state]
        friend = friends[i]
        start_time = end_time - friend['min_duration']
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": minutes_to_time_str(start_time),
            "end_time": minutes_to_time_str(end_time)
        })
        state = parent[state]
    # Add the first meeting
    mask, i = state
    end_time = dp[state]
    friend = friends[i]
    start_time = end_time - friend['min_duration']
    itinerary.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": minutes_to_time_str(start_time),
        "end_time": minutes_to_time_str(end_time)
    })
    # Reverse to get chronological order
    itinerary.reverse()

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result))