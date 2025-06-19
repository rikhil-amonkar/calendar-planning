import json

district_names = [
    "Marina District",
    "Bayview",
    "Sunset District",
    "Richmond District",
    "Nob Hill",
    "Chinatown",
    "Haight-Ashbury",
    "North Beach",
    "Russian Hill",
    "Embarcadero"
]

travel_matrix = [
    [0, 27, 19, 11, 12, 15, 16, 11, 8, 14],
    [27, 0, 23, 25, 20, 19, 19, 22, 23, 19],
    [21, 22, 0, 12, 27, 30, 15, 28, 24, 30],
    [9, 27, 11, 0, 17, 20, 10, 17, 13, 19],
    [11, 19, 24, 14, 0, 6, 13, 8, 5, 9],
    [12, 20, 29, 20, 9, 0, 19, 3, 7, 5],
    [17, 18, 15, 10, 15, 19, 0, 19, 17, 20],
    [9, 25, 27, 18, 7, 6, 18, 0, 4, 6],
    [7, 23, 23, 14, 5, 9, 17, 5, 0, 8],
    [12, 21, 30, 21, 10, 7, 21, 5, 8, 0]
]

friends = [
    ("Charles", 1, 45, 690, 870),
    ("Robert", 2, 30, 1005, 1260),
    ("Karen", 3, 60, 1155, 1290),
    ("Rebecca", 4, 90, 975, 1230),
    ("Margaret", 5, 120, 855, 1185),
    ("Patricia", 6, 45, 870, 1230),
    ("Mark", 7, 105, 840, 1110),
    ("Melissa", 8, 30, 780, 1185),
    ("Laura", 9, 105, 465, 795)
]

# Sort friends by window start time to optimize DP exploration
friends_sorted = sorted(friends, key=lambda x: x[3])
n_friends = len(friends_sorted)
n_districts = len(district_names)

INF = 10**9
dp = [[INF] * n_districts for _ in range(1 << n_friends)]
parent = [[None] * n_districts for _ in range(1 << n_friends)]

# Start at Marina (index 0) at 9:00 AM (540 minutes)
dp[0][0] = 540

for mask in range(1 << n_friends):
    for loc in range(n_districts):
        if dp[mask][loc] == INF:
            continue
        for i in range(n_friends):
            if mask & (1 << i):
                continue
            next_loc = friends_sorted[i][1]
            travel_dur = travel_matrix[loc][next_loc]
            arrival_time = dp[mask][loc] + travel_dur
            win_start = friends_sorted[i][3]
            win_end = friends_sorted[i][4]
            min_dur = friends_sorted[i][2]
            start_meeting = max(arrival_time, win_start)
            end_meeting = start_meeting + min_dur
            if end_meeting <= win_end:
                new_mask = mask | (1 << i)
                if end_meeting < dp[new_mask][next_loc]:
                    dp[new_mask][next_loc] = end_meeting
                    parent[new_mask][next_loc] = (mask, loc, i, start_meeting, end_meeting)

best_mask = 0
best_count = 0
best_arrival_back = INF
best_loc = 0

for mask in range(1 << n_friends):
    count = bin(mask).count("1")
    for loc in range(n_districts):
        if dp[mask][loc] == INF:
            continue
        return_time = travel_matrix[loc][0]
        arrival_back = dp[mask][loc] + return_time
        if arrival_back > 1260:  # Must return by 9:00 PM
            continue
        if count > best_count or (count == best_count and arrival_back < best_arrival_back):
            best_count = count
            best_arrival_back = arrival_back
            best_mask = mask
            best_loc = loc

itinerary = []
if best_count > 0:
    mask = best_mask
    loc = best_loc
    meetings = []
    while mask != 0:
        if parent[mask][loc] is None:
            break
        prev_mask, prev_loc, friend_i, start_meeting, end_meeting = parent[mask][loc]
        meetings.append((friend_i, start_meeting, end_meeting, loc))
        mask = prev_mask
        loc = prev_loc
    meetings.reverse()
    for meet in meetings:
        friend_i, start, end, loc_index = meet
        friend_name = friends_sorted[friend_i][0]
        loc_name = district_names[loc_index]
        hour_start = start // 60
        min_start = start % 60
        hour_end = end // 60
        min_end = end % 60
        start_str = f"{hour_start}:{min_start:02d}"
        end_str = f"{hour_end}:{min_end:02d}"
        itinerary.append({
            "action": "meet",
            "location": loc_name,
            "person": friend_name,
            "start_time": start_str,
            "end_time": end_str
        })

result = {
    "itinerary": itinerary
}
print(json.dumps(result))