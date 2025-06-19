import json

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Define travel_time matrix (11x11)
travel_time = [
    [0, 6, 5, 8, 12, 21, 11, 21, 20, 10, 25],   # Embarcadero (0)
    [8, 0, 11, 7, 9, 18, 12, 22, 17, 11, 27],    # Fisherman's Wharf (1)
    [4, 10, 0, 11, 15, 21, 13, 19, 22, 8, 20],   # Financial District (2)
    [8, 7, 11, 0, 7, 14, 7, 17, 14, 5, 21],      # Russian Hill (3)
    [14, 10, 17, 8, 0, 11, 7, 16, 10, 12, 22],   # Marina District (4)
    [19, 18, 22, 13, 9, 0, 10, 10, 7, 17, 16],   # Richmond District (5)
    [10, 13, 13, 7, 6, 12, 0, 11, 11, 8, 16],    # Pacific Heights (6)
    [20, 23, 21, 17, 17, 10, 12, 0, 15, 15, 6],  # Haight-Ashbury (7)
    [20, 19, 23, 14, 11, 7, 11, 15, 0, 18, 21],  # Presidio (8)
    [9, 10, 9, 5, 11, 14, 8, 13, 17, 0, 17],     # Nob Hill (9)
    [22, 24, 21, 18, 21, 16, 16, 6, 20, 16, 0]   # The Castro (10)
]

# Friend data
friends = [
    {"name": "Stephanie", "location": "Fisherman's Wharf", "start": 15*60+30, "end": 22*60, "min_duration": 30, "loc_index": 1},
    {"name": "Lisa", "location": "Financial District", "start": 10*60+45, "end": 17*60+15, "min_duration": 15, "loc_index": 2},
    {"name": "Melissa", "location": "Russian Hill", "start": 17*60, "end": 21*60+45, "min_duration": 120, "loc_index": 3},
    {"name": "Betty", "location": "Marina District", "start": 10*60+45, "end": 14*60+15, "min_duration": 60, "loc_index": 4},
    {"name": "Sarah", "location": "Richmond District", "start": 16*60+15, "end": 19*60+30, "min_duration": 105, "loc_index": 5},
    {"name": "Daniel", "location": "Pacific Heights", "start": 18*60+30, "end": 21*60+45, "min_duration": 60, "loc_index": 6},
    {"name": "Joshua", "location": "Haight-Ashbury", "start": 9*60, "end": 15*60+30, "min_duration": 15, "loc_index": 7},
    {"name": "Joseph", "location": "Presidio", "start": 7*60, "end": 13*60, "min_duration": 45, "loc_index": 8},
    {"name": "Andrew", "location": "Nob Hill", "start": 19*60+45, "end": 22*60, "min_duration": 105, "loc_index": 9},
    {"name": "John", "location": "The Castro", "start": 13*60+15, "end": 19*60+45, "min_duration": 45, "loc_index": 10}
]

n = len(friends)  # 10
num_locations = 11  # 0 to 10
INF = 10**9

# Initialize DP and parent structures
dp = [[INF] * num_locations for _ in range(1 << n)]
parent = [[None] * num_locations for _ in range(1 << n)]

# Base state: start at Embarcadero (index 0) at 9:00 AM (540 minutes)
dp[0][0] = 540

# Run DP
for mask in range(1 << n):
    for loc in range(num_locations):
        if dp[mask][loc] >= INF:
            continue
        for j in range(n):
            if mask & (1 << j):
                continue
            friend = friends[j]
            next_loc = friend['loc_index']
            travel = travel_time[loc][next_loc]
            arrival = dp[mask][loc] + travel
            start_meeting = max(arrival, friend['start'])
            if start_meeting + friend['min_duration'] <= friend['end']:
                finish = start_meeting + friend['min_duration']
                new_mask = mask | (1 << j)
                if finish < dp[new_mask][next_loc]:
                    dp[new_mask][next_loc] = finish
                    parent[new_mask][next_loc] = (mask, loc, j, start_meeting)

# Find best state (max count of meetings)
best_mask = 0
best_loc = 0
best_count = -1
for mask in range(1 << n):
    for loc in range(num_locations):
        if dp[mask][loc] < INF:
            count = bin(mask).count("1")
            if count > best_count:
                best_count = count
                best_mask = mask
                best_loc = loc

# Reconstruct itinerary
itinerary = []
if best_count > 0:
    current_mask = best_mask
    current_loc = best_loc
    stack = []
    while current_mask != 0:
        if parent[current_mask][current_loc] is None:
            break
        prev_mask, prev_loc, friend_index, start_time = parent[current_mask][current_loc]
        friend = friends[friend_index]
        stack.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": format_time(start_time),
            "end_time": format_time(start_time + friend['min_duration'])
        })
        current_mask = prev_mask
        current_loc = prev_loc
    itinerary = stack[::-1]

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result))