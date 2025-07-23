import json

def minutes_to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours}:{minutes:02d}"

travel_times = {
    "Union Square": {
        "Russian Hill": 13,
        "Alamo Square": 15,
        "Haight-Ashbury": 18,
        "Marina District": 18,
        "Bayview": 15,
        "Chinatown": 7,
        "Presidio": 24,
        "Sunset District": 27
    },
    "Russian Hill": {
        "Union Square": 10,
        "Alamo Square": 15,
        "Haight-Ashbury": 17,
        "Marina District": 7,
        "Bayview": 23,
        "Chinatown": 9,
        "Presidio": 14,
        "Sunset District": 23
    },
    "Alamo Square": {
        "Union Square": 14,
        "Russian Hill": 13,
        "Haight-Ashbury": 5,
        "Marina District": 15,
        "Bayview": 16,
        "Chinatown": 15,
        "Presidio": 17,
        "Sunset District": 16
    },
    "Haight-Ashbury": {
        "Union Square": 19,
        "Russian Hill": 17,
        "Alamo Square": 5,
        "Marina District": 17,
        "Bayview": 18,
        "Chinatown": 19,
        "Presidio": 15,
        "Sunset District": 15
    },
    "Marina District": {
        "Union Square": 16,
        "Russian Hill": 8,
        "Alamo Square": 15,
        "Haight-Ashbury": 16,
        "Bayview": 27,
        "Chinatown": 15,
        "Presidio": 10,
        "Sunset District": 19
    },
    "Bayview": {
        "Union Square": 18,
        "Russian Hill": 23,
        "Alamo Square": 16,
        "Haight-Ashbury": 19,
        "Marina District": 27,
        "Chinatown": 19,
        "Presidio": 32,
        "Sunset District": 23
    },
    "Chinatown": {
        "Union Square": 7,
        "Russian Hill": 7,
        "Alamo Square": 17,
        "Haight-Ashbury": 19,
        "Marina District": 12,
        "Bayview": 20,
        "Presidio": 19,
        "Sunset District": 29
    },
    "Presidio": {
        "Union Square": 22,
        "Russian Hill": 14,
        "Alamo Square": 19,
        "Haight-Ashbury": 15,
        "Marina District": 11,
        "Bayview": 31,
        "Chinatown": 21,
        "Sunset District": 15
    },
    "Sunset District": {
        "Union Square": 30,
        "Russian Hill": 24,
        "Alamo Square": 17,
        "Haight-Ashbury": 15,
        "Marina District": 21,
        "Bayview": 22,
        "Chinatown": 30,
        "Presidio": 16
    }
}

friends = [
    {"name": "Betty", "location": "Russian Hill", "start": 420, "end": 1005, "duration": 105},
    {"name": "Melissa", "location": "Alamo Square", "start": 570, "end": 1035, "duration": 105},
    {"name": "Joshua", "location": "Haight-Ashbury", "start": 735, "end": 1140, "duration": 90},
    {"name": "Jeffrey", "location": "Marina District", "start": 735, "end": 1080, "duration": 45},
    {"name": "James", "location": "Bayview", "start": 450, "end": 1200, "duration": 90},
    {"name": "Anthony", "location": "Chinatown", "start": 705, "end": 810, "duration": 75},
    {"name": "Timothy", "location": "Presidio", "start": 750, "end": 885, "duration": 90},
    {"name": "Emily", "location": "Sunset District", "start": 1170, "end": 1290, "duration": 120}
]

n = len(friends)
n_masks = 1 << n
dp = [[10**9] * 9 for _ in range(n_masks)]
parent = [[None] * 9 for _ in range(n_masks)]

dp[0][8] = 540

for mask in range(n_masks):
    for loc in range(9):
        if dp[mask][loc] == 10**9:
            continue
        current_time = dp[mask][loc]
        current_loc_name = "Union Square" if loc == 8 else friends[loc]['location']
        
        for next_idx in range(n):
            if mask & (1 << next_idx):
                continue
            next_friend = friends[next_idx]
            next_loc_name = next_friend['location']
            tt = travel_times[current_loc_name][next_loc_name]
            arrival_time = current_time + tt
            start_time = max(arrival_time, next_friend['start'])
            end_time = start_time + next_friend['duration']
            
            if end_time <= next_friend['end']:
                new_mask = mask | (1 << next_idx)
                if end_time < dp[new_mask][next_idx]:
                    dp[new_mask][next_idx] = end_time
                    parent[new_mask][next_idx] = (mask, loc, start_time, end_time)

best_mask = None
best_loc = None
max_count = -1
for mask in range(n_masks):
    count = bin(mask).count("1")
    for loc in range(8):
        if dp[mask][loc] < 10**9:
            if count > max_count:
                max_count = count
                best_mask = mask
                best_loc = loc

itinerary = []
if best_mask is not None:
    mask = best_mask
    loc = best_loc
    while mask != 0:
        prev_mask, prev_loc, start_time, end_time = parent[mask][loc]
        friend = friends[loc]
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": minutes_to_time(start_time),
            "end_time": minutes_to_time(end_time)
        })
        mask = prev_mask
        loc = prev_loc
    itinerary.reverse()

result = {"itinerary": itinerary}
print(json.dumps(result))