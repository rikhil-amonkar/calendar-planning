import json

def main():
    locations = [
        "Richmond District", "The Castro", "Nob Hill", "Marina District", "Pacific Heights",
        "Haight-Ashbury", "Mission District", "Chinatown", "Russian Hill", "Alamo Square", "Bayview"
    ]
    
    travel_times = {
        "Richmond District": {
            "The Castro": 16, "Nob Hill": 17, "Marina District": 9, "Pacific Heights": 10,
            "Haight-Ashbury": 10, "Mission District": 20, "Chinatown": 20, "Russian Hill": 13,
            "Alamo Square": 13, "Bayview": 27
        },
        "The Castro": {
            "Richmond District": 16, "Nob Hill": 16, "Marina District": 21, "Pacific Heights": 16,
            "Haight-Ashbury": 6, "Mission District": 7, "Chinatown": 22, "Russian Hill": 18,
            "Alamo Square": 8, "Bayview": 19
        },
        "Nob Hill": {
            "Richmond District": 14, "The Castro": 17, "Marina District": 11, "Pacific Heights": 8,
            "Haight-Ashbury": 13, "Mission District": 13, "Chinatown": 6, "Russian Hill": 5,
            "Alamo Square": 11, "Bayview": 19
        },
        "Marina District": {
            "Richmond District": 11, "The Castro": 22, "Nob Hill": 12, "Pacific Heights": 7,
            "Haight-Ashbury": 16, "Mission District": 20, "Chinatown": 15, "Russian Hill": 8,
            "Alamo Square": 15, "Bayview": 27
        },
        "Pacific Heights": {
            "Richmond District": 12, "The Castro": 16, "Nob Hill": 8, "Marina District": 6,
            "Haight-Ashbury": 11, "Mission District": 15, "Chinatown": 11, "Russian Hill": 7,
            "Alamo Square": 10, "Bayview": 22
        },
        "Haight-Ashbury": {
            "Richmond District": 10, "The Castro": 6, "Nob Hill": 15, "Marina District": 17,
            "Pacific Heights": 12, "Mission District": 11, "Chinatown": 19, "Russian Hill": 17,
            "Alamo Square": 5, "Bayview": 18
        },
        "Mission District": {
            "Richmond District": 20, "The Castro": 7, "Nob Hill": 12, "Marina District": 19,
            "Pacific Heights": 16, "Haight-Ashbury": 12, "Chinatown": 16, "Russian Hill": 15,
            "Alamo Square": 11, "Bayview": 14
        },
        "Chinatown": {
            "Richmond District": 20, "The Castro": 22, "Nob Hill": 9, "Marina District": 12,
            "Pacific Heights": 10, "Haight-Ashbury": 19, "Mission District": 17, "Russian Hill": 7,
            "Alamo Square": 17, "Bayview": 20
        },
        "Russian Hill": {
            "Richmond District": 14, "The Castro": 21, "Nob Hill": 5, "Marina District": 7,
            "Pacific Heights": 7, "Haight-Ashbury": 17, "Mission District": 16, "Chinatown": 9,
            "Alamo Square": 15, "Bayview": 23
        },
        "Alamo Square": {
            "Richmond District": 11, "The Castro": 8, "Nob Hill": 11, "Marina District": 15,
            "Pacific Heights": 10, "Haight-Ashbury": 5, "Mission District": 10, "Chinatown": 15,
            "Russian Hill": 13, "Bayview": 16
        },
        "Bayview": {
            "Richmond District": 25, "The Castro": 19, "Nob Hill": 20, "Marina District": 27,
            "Pacific Heights": 23, "Haight-Ashbury": 19, "Mission District": 13, "Chinatown": 19,
            "Russian Hill": 23, "Alamo Square": 16
        }
    }
    
    # Adjust to use maximum travel time for symmetry to satisfy constraints
    for i in range(len(locations)):
        for j in range(i + 1, len(locations)):
            loc_i = locations[i]
            loc_j = locations[j]
            time_ij = travel_times[loc_i][loc_j]
            time_ji = travel_times[loc_j][loc_i]
            max_time = max(time_ij, time_ji)  # Use max to ensure sufficient travel time
            travel_times[loc_i][loc_j] = max_time
            travel_times[loc_j][loc_i] = max_time
    
    for loc in locations:
        travel_times[loc][loc] = 0
    
    loc_to_index = {loc: idx for idx, loc in enumerate(locations)}
    
    friends = [
        {"name": "Matthew", "location": "The Castro", "start": 450, "end": 660, "min_time": 45},
        {"name": "Rebecca", "location": "Nob Hill", "start": 375, "end": 615, "min_time": 105},
        {"name": "Brian", "location": "Marina District", "start": 315, "end": 780, "min_time": 30},
        {"name": "Emily", "location": "Pacific Heights", "start": 135, "end": 645, "min_time": 15},
        {"name": "Karen", "location": "Haight-Ashbury", "start": 165, "end": 510, "min_time": 30},
        {"name": "Stephanie", "location": "Mission District", "start": 240, "end": 405, "min_time": 75},
        {"name": "James", "location": "Chinatown", "start": 330, "end": 600, "min_time": 120},
        {"name": "Steven", "location": "Russian Hill", "start": 300, "end": 660, "min_time": 30},
        {"name": "Elizabeth", "location": "Alamo Square", "start": 240, "end": 495, "min_time": 120},
        {"name": "William", "location": "Bayview", "start": 555, "end": 675, "min_time": 90}
    ]
    
    n = len(friends)
    INF = 10**9
    dp = [[INF] * len(locations) for _ in range(1 << n)]
    parent = [[None] * len(locations) for _ in range(1 << n)]
    
    dp[0][0] = 0
    
    for mask in range(1 << n):
        for loc_idx in range(len(locations)):
            if dp[mask][loc_idx] == INF:
                continue
            current_loc = locations[loc_idx]
            for friend_idx in range(n):
                if mask & (1 << friend_idx):
                    continue
                friend = friends[friend_idx]
                next_loc = friend["location"]
                travel_time = travel_times[current_loc][next_loc]
                arrival_time = dp[mask][loc_idx] + travel_time
                start_time = max(arrival_time, friend["start"])
                end_time = start_time + friend["min_time"]
                if end_time > friend["end"]:
                    continue
                next_loc_idx = loc_to_index[next_loc]
                new_mask = mask | (1 << friend_idx)
                if end_time < dp[new_mask][next_loc_idx]:
                    dp[new_mask][next_loc_idx] = end_time
                    parent[new_mask][next_loc_idx] = (mask, loc_idx, friend_idx, start_time, end_time)
    
    best_count = -1
    best_mask = None
    best_loc_idx = None
    for mask in range(1 << n):
        count = bin(mask).count("1")
        for loc_idx in range(len(locations)):
            if dp[mask][loc_idx] == INF:
                continue
            current_time = dp[mask][loc_idx]
            return_time = travel_times[locations[loc_idx]]["Richmond District"]
            if current_time + return_time <= 720:
                if count > best_count:
                    best_count = count
                    best_mask = mask
                    best_loc_idx = loc_idx
    
    itinerary_entries = []
    mask = best_mask
    loc_idx = best_loc_idx
    while mask != 0:
        if parent[mask][loc_idx] is None:
            break
        prev_mask, prev_loc_idx, friend_idx, start_time, end_time = parent[mask][loc_idx]
        friend = friends[friend_idx]
        hour_start = start_time // 60 + 9
        min_start = start_time % 60
        start_str = f"{hour_start}:{min_start:02d}"
        hour_end = end_time // 60 + 9
        min_end = end_time % 60
        end_str = f"{hour_end}:{min_end:02d}"
        entry = {
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": start_str,
            "end_time": end_str
        }
        itinerary_entries.append(entry)
        mask = prev_mask
        loc_idx = prev_loc_idx
    
    itinerary_entries.reverse()
    output = {"itinerary": itinerary_entries}
    print(json.dumps(output, separators=(',', ':')))

if __name__ == "__main__":
    main()