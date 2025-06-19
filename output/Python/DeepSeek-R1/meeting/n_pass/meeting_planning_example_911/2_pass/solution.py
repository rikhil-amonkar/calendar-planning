import json

def time_to_minutes(s):
    s = s.strip()
    if s.endswith('AM') or s.endswith('PM'):
        time_part = s[:-2].strip()
        am_pm = s[-2:]
    else:
        time_part = s
        am_pm = ''
    parts = time_part.split(':')
    h = int(parts[0])
    m = int(parts[1]) if len(parts) > 1 else 0
    if am_pm == 'PM' and h != 12:
        h += 12
    if am_pm == 'AM' and h == 12:
        h = 0
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

location_names = [
    "North Beach",
    "Golden Gate Park",
    "Embarcadero",
    "Haight-Ashbury",
    "Richmond District",
    "Nob Hill",
    "Marina District",
    "Presidio",
    "Union Square",
    "Financial District",
    "The Castro"
]

travel_dict = {
    "The Castro": {
        "North Beach": 20,
        "Golden Gate Park": 11,
        "Embarcadero": 22,
        "Haight-Ashbury": 6,
        "Richmond District": 16,
        "Nob Hill": 16,
        "Marina District": 21,
        "Presidio": 20,
        "Union Square": 19,
        "Financial District": 21
    },
    "North Beach": {
        "The Castro": 23,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Haight-Ashbury": 18,
        "Richmond District": 18,
        "Nob Hill": 7,
        "Marina District": 9,
        "Presidio": 17,
        "Union Square": 7,
        "Financial District": 8
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "North Beach": 23,
        "Embarcadero": 25,
        "Haight-Ashbury": 7,
        "Richmond District": 7,
        "Nob Hill": 20,
        "Marina District": 16,
        "Presidio": 11,
        "Union Square": 22,
        "Financial District": 26
    },
    "Embarcadero": {
        "The Castro": 25,
        "North Beach": 5,
        "Golden Gate Park": 25,
        "Haight-Ashbury": 21,
        "Richmond District": 21,
        "Nob Hill": 10,
        "Marina District": 12,
        "Presidio": 20,
        "Union Square": 10,
        "Financial District": 5
    },
    "Haight-Ashbury": {
        "The Castro": 6,
        "North Beach": 19,
        "Golden Gate Park": 7,
        "Embarcadero": 20,
        "Richmond District": 10,
        "Nob Hill": 15,
        "Marina District": 17,
        "Presidio": 15,
        "Union Square": 19,
        "Financial District": 21
    },
    "Richmond District": {
        "The Castro": 16,
        "North Beach": 17,
        "Golden Gate Park": 9,
        "Embarcadero": 19,
        "Haight-Ashbury": 10,
        "Nob Hill": 17,
        "Marina District": 9,
        "Presidio": 7,
        "Union Square": 21,
        "Financial District": 22
    },
    "Nob Hill": {
        "The Castro": 17,
        "North Beach": 8,
        "Golden Gate Park": 17,
        "Embarcadero": 9,
        "Haight-Ashbury": 13,
        "Richmond District": 14,
        "Marina District": 11,
        "Presidio": 17,
        "Union Square": 7,
        "Financial District": 9
    },
    "Marina District": {
        "The Castro": 22,
        "North Beach": 11,
        "Golden Gate Park": 18,
        "Embarcadero": 14,
        "Haight-Ashbury": 16,
        "Richmond District": 11,
        "Nob Hill": 12,
        "Presidio": 10,
        "Union Square": 16,
        "Financial District": 17
    },
    "Presidio": {
        "The Castro": 21,
        "North Beach": 18,
        "Golden Gate Park": 12,
        "Embarcadero": 20,
        "Haight-Ashbury": 15,
        "Richmond District": 7,
        "Nob Hill": 18,
        "Marina District": 11,
        "Union Square": 22,
        "Financial District": 23
    },
    "Union Square": {
        "The Castro": 17,
        "North Beach": 10,
        "Golden Gate Park": 22,
        "Embarcadero": 11,
        "Haight-Ashbury": 18,
        "Richmond District": 20,
        "Nob Hill": 9,
        "Marina District": 18,
        "Presidio": 24,
        "Financial District": 9
    },
    "Financial District": {
        "The Castro": 20,
        "North Beach": 7,
        "Golden Gate Park": 23,
        "Embarcadero": 4,
        "Haight-Ashbury": 19,
        "Richmond District": 21,
        "Nob Hill": 8,
        "Marina District": 15,
        "Presidio": 22,
        "Union Square": 9
    }
}

friends = [
    ("Steven", "North Beach", time_to_minutes("5:30PM"), time_to_minutes("8:30PM"), 15),
    ("Sarah", "Golden Gate Park", time_to_minutes("5:00PM"), time_to_minutes("7:15PM"), 75),
    ("Brian", "Embarcadero", time_to_minutes("2:15PM"), time_to_minutes("4:00PM"), 105),
    ("Stephanie", "Haight-Ashbury", time_to_minutes("10:15AM"), time_to_minutes("12:15PM"), 75),
    ("Melissa", "Richmond District", time_to_minutes("2:00PM"), time_to_minutes("7:30PM"), 30),
    ("Nancy", "Nob Hill", time_to_minutes("8:15AM"), time_to_minutes("12:45PM"), 90),
    ("David", "Marina District", time_to_minutes("11:15AM"), time_to_minutes("1:15PM"), 120),
    ("James", "Presidio", time_to_minutes("3:00PM"), time_to_minutes("6:15PM"), 120),
    ("Elizabeth", "Union Square", time_to_minutes("11:30AM"), time_to_minutes("9:00PM"), 60),
    ("Robert", "Financial District", time_to_minutes("1:15PM"), time_to_minutes("3:15PM"), 45)
]

# Sort friends by their availability end time
friends.sort(key=lambda x: x[3])

n = len(friends)
location_index = {name: idx for idx, name in enumerate(location_names)}

travel_time = [[0] * len(location_names) for _ in range(len(location_names))]
for i, from_loc in enumerate(location_names):
    for j, to_loc in enumerate(location_names):
        if from_loc == to_loc:
            travel_time[i][j] = 0
        else:
            travel_time[i][j] = travel_dict[from_loc][to_loc]

dp = [[10**9] * n for _ in range(1 << n)]
parent = [[(-1, -1)] * n for _ in range(1 << n)]

start_time = time_to_minutes("9:00AM")
home = "The Castro"

for j in range(n):
    loc_j = friends[j][1]
    travel = travel_dict[home][loc_j]
    start_meet = max(start_time + travel, friends[j][2])
    end_meet = start_meet + friends[j][4]
    if end_meet <= friends[j][3]:
        mask = 1 << j
        dp[mask][j] = end_meet
        parent[mask][j] = (-1, -1)

for mask in range(1 << n):
    for j in range(n):
        if dp[mask][j] == 10**9:
            continue
        for k in range(n):
            if mask & (1 << k):
                continue
            loc_j = friends[j][1]
            loc_k = friends[k][1]
            idx_j = location_index[loc_j]
            idx_k = location_index[loc_k]
            travel = travel_time[idx_j][idx_k]
            arrival = dp[mask][j] + travel
            start_meet_k = max(arrival, friends[k][2])
            end_meet_k = start_meet_k + friends[k][4]
            if end_meet_k > friends[k][3]:
                continue
            new_mask = mask | (1 << k)
            if end_meet_k < dp[new_mask][k]:
                dp[new_mask][k] = end_meet_k
                parent[new_mask][k] = (mask, j)

best_mask = 0
best_count = -1
best_j = -1
for mask in range(1 << n):
    count = bin(mask).count("1")
    for j in range(n):
        if dp[mask][j] < 10**9:
            if count > best_count:
                best_count = count
                best_mask = mask
                best_j = j

itinerary = []
current_mask = best_mask
current_j = best_j

while current_mask != 0 and current_j != -1:
    end_time_val = dp[current_mask][current_j]
    start_time_val = end_time_val - friends[current_j][4]
    person = friends[current_j][0]
    location = friends[current_j][1]
    itinerary.append({
        "action": "meet",
        "location": location,
        "person": person,
        "start_time": minutes_to_time(start_time_val),
        "end_time": minutes_to_time(end_time_val)
    })
    prev_mask, prev_j = parent[current_mask][current_j]
    current_mask, current_j = prev_mask, prev_j

itinerary.reverse()

result = {
    "itinerary": itinerary
}

print(json.dumps(result))