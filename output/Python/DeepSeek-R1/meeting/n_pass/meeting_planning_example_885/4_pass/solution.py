import json

def main():
    locations = [
        "Russian Hill",
        "Marina District",
        "Financial District",
        "Alamo Square",
        "Golden Gate Park",
        "The Castro",
        "Bayview",
        "Sunset District",
        "Haight-Ashbury",
        "Nob Hill"
    ]
    
    dist = [
        [0, 7, 11, 15, 21, 21, 23, 23, 17, 5],
        [8, 0, 17, 15, 18, 22, 27, 19, 16, 12],
        [11, 15, 0, 17, 23, 20, 19, 30, 19, 8],
        [13, 15, 17, 0, 9, 8, 16, 16, 5, 11],
        [19, 16, 26, 9, 0, 13, 23, 10, 7, 20],
        [18, 21, 21, 8, 11, 0, 19, 17, 6, 16],
        [23, 27, 19, 16, 22, 19, 0, 23, 19, 20],
        [24, 21, 30, 17, 11, 17, 22, 0, 15, 27],
        [17, 17, 21, 5, 7, 6, 18, 15, 0, 15],
        [5, 11, 9, 11, 17, 17, 19, 24, 13, 0]
    ]
    
    friends_info = [
        {"name": "Mark", "location_index": 1, "available_start": 1125, "available_end": 1260, "min_duration": 90},
        {"name": "Karen", "location_index": 2, "available_start": 570, "available_end": 765, "min_duration": 90},
        {"name": "Barbara", "location_index": 3, "available_start": 600, "available_end": 1170, "min_duration": 90},
        {"name": "Nancy", "location_index": 4, "available_start": 1005, "available_end": 1200, "min_duration": 105},
        {"name": "David", "location_index": 5, "available_start": 540, "available_end": 1080, "min_duration": 120},
        {"name": "Linda", "location_index": 6, "available_start": 1095, "available_end": 1185, "min_duration": 45},
        {"name": "Kevin", "location_index": 7, "available_start": 600, "available_end": 1065, "min_duration": 120},
        {"name": "Matthew", "location_index": 8, "available_start": 615, "available_end": 930, "min_duration": 45},
        {"name": "Andrew", "location_index": 9, "available_start": 705, "available_end": 1005, "min_duration": 105}
    ]
    
    n_friends = len(friends_info)
    n_masks = 1 << n_friends
    BIG = 10**9
    
    # DP state: dp[mask][j] = (end_time, prev_mask, prev_index, start_time, end_time)
    dp = [[(BIG, -1, -1, 0, 0) for _ in range(n_friends)] for _ in range(n_masks)]
    
    # Initialize DP with first meetings from the hotel
    for j in range(n_friends):
        loc_j = friends_info[j]["location_index"]
        travel_time = dist[0][loc_j]
        start_time = max(540 + travel_time, friends_info[j]["available_start"])
        end_time = start_time + friends_info[j]["min_duration"]
        if end_time <= friends_info[j]["available_end"]:
            mask = 1 << j
            dp[mask][j] = (end_time, 0, -1, start_time, end_time)
    
    # DP transitions: extend existing schedules only if current meeting count < 5
    for mask in range(n_masks):
        for j in range(n_friends):
            if dp[mask][j][0] == BIG:
                continue
            current_count = bin(mask).count("1")
            # Skip transitions if already at 5 meetings
            if current_count < 5:
                for k in range(n_friends):
                    if mask & (1 << k):
                        continue
                    loc_j = friends_info[j]["location_index"]
                    loc_k = friends_info[k]["location_index"]
                    travel_time = dist[loc_j][loc_k]
                    arrival_time = dp[mask][j][0] + travel_time
                    start_k = max(arrival_time, friends_info[k]["available_start"])
                    end_k = start_k + friends_info[k]["min_duration"]
                    if end_k <= friends_info[k]["available_end"]:
                        new_mask = mask | (1 << k)
                        if end_k < dp[new_mask][k][0]:
                            dp[new_mask][k] = (end_k, mask, j, start_k, end_k)
    
    # Find optimal schedule that returns to hotel by 21:00
    best_mask = 0
    best_j = -1
    best_count = 0
    best_return_time = BIG
    for mask in range(n_masks):
        for j in range(n_friends):
            if dp[mask][j][0] == BIG:
                continue
            loc_j = friends_info[j]["location_index"]
            travel_back = dist[loc_j][0]
            return_time = dp[mask][j][0] + travel_back
            if return_time > 1260:
                continue
            count = bin(mask).count("1")
            # Maximize meeting count, then minimize return time
            if count > best_count or (count == best_count and return_time < best_return_time):
                best_count = count
                best_return_time = return_time
                best_mask = mask
                best_j = j
    
    # Reconstruct meeting schedule
    meetings = []
    current_mask = best_mask
    current_j = best_j
    while current_j != -1:
        state = dp[current_mask][current_j]
        meeting = {
            "person": friends_info[current_j]["name"],
            "location": locations[friends_info[current_j]["location_index"]],
            "start_time": state[3],
            "end_time": state[4]
        }
        meetings.append(meeting)
        next_mask = state[1]
        next_j = state[2]
        current_mask = next_mask
        current_j = next_j
    meetings.reverse()
    
    # Convert minutes to HH:MM format
    def min_to_time(m):
        h = m // 60
        mm = m % 60
        return f"{h}:{mm:02d}"
    
    # Prepare JSON output
    itinerary_json = []
    for meet in meetings:
        itinerary_json.append({
            "action": "meet",
            "location": meet["location"],
            "person": meet["person"],
            "start_time": min_to_time(meet["start_time"]),
            "end_time": min_to_time(meet["end_time"])
        })
    
    result = {"itinerary": itinerary_json}
    print(json.dumps(result))

if __name__ == "__main__":
    main()