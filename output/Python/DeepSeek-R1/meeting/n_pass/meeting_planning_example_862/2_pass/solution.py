import json

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    locations = [
        "Mission District",
        "Alamo Square",
        "Presidio",
        "Russian Hill",
        "North Beach",
        "Golden Gate Park",
        "Richmond District",
        "Embarcadero",
        "Financial District",
        "Marina District"
    ]
    
    travel_time = [
        [0, 11, 25, 15, 17, 17, 20, 19, 15, 19],
        [10, 0, 17, 13, 15, 9, 11, 16, 17, 15],
        [26, 19, 0, 14, 18, 12, 7, 20, 23, 11],
        [16, 15, 14, 0, 5, 21, 14, 8, 11, 7],
        [18, 16, 17, 4, 0, 22, 18, 6, 8, 9],
        [17, 9, 11, 19, 23, 0, 7, 25, 26, 16],
        [20, 13, 7, 13, 17, 9, 0, 19, 22, 9],
        [20, 19, 20, 8, 5, 25, 21, 0, 5, 12],
        [17, 17, 22, 11, 7, 23, 21, 4, 0, 15],
        [20, 15, 10, 8, 11, 18, 11, 14, 17, 0]
    ]
    
    friends = [
        {"name": "Laura", "location": 1, "start": 870, "end": 975, "duration": 75},
        {"name": "Brian", "location": 2, "start": 615, "end": 1020, "duration": 30},
        {"name": "Karen", "location": 3, "start": 1080, "end": 1215, "duration": 90},
        {"name": "Stephanie", "location": 4, "start": 615, "end": 960, "duration": 75},
        {"name": "Helen", "location": 5, "start": 690, "end": 1305, "duration": 120},
        {"name": "Sandra", "location": 6, "start": 480, "end": 915, "duration": 30},
        {"name": "Mary", "location": 7, "start": 1005, "end": 1125, "duration": 120},
        {"name": "Deborah", "location": 8, "start": 1140, "end": 1245, "duration": 105},
        {"name": "Elizabeth", "location": 9, "start": 510, "end": 795, "duration": 105}
    ]
    
    n = len(friends)
    n_locations = 10
    
    dp = [[10**9] * n_locations for _ in range(1 << n)]
    dp[0][0] = 540
    parent = [[None] * n_locations for _ in range(1 << n)]
    
    for mask in range(1 << n):
        for loc in range(n_locations):
            if dp[mask][loc] == 10**9:
                continue
            for j in range(n):
                if mask & (1 << j):
                    continue
                friend_loc = friends[j]["location"]
                t = travel_time[loc][friend_loc]
                arrival_time = dp[mask][loc] + t
                start_meeting = max(arrival_time, friends[j]["start"])
                end_meeting = start_meeting + friends[j]["duration"]
                if end_meeting <= friends[j]["end"]:
                    new_mask = mask | (1 << j)
                    if end_meeting < dp[new_mask][friend_loc]:
                        dp[new_mask][friend_loc] = end_meeting
                        parent[new_mask][friend_loc] = (mask, loc, j, start_meeting, end_meeting)
    
    best_mask = None
    best_count = -1
    best_loc = -1
    best_time = 10**9
    for mask in range(1 << n):
        count = bin(mask).count("1")
        for loc in range(n_locations):
            if dp[mask][loc] < 10**9:
                if count > best_count or (count == best_count and dp[mask][loc] < best_time):
                    best_count = count
                    best_mask = mask
                    best_loc = loc
                    best_time = dp[mask][loc]
    
    itinerary = []
    cur_mask = best_mask
    cur_loc = best_loc
    while cur_mask != 0 and parent[cur_mask][cur_loc] is not None:
        prev_mask, prev_loc, j, start_meeting, end_meeting = parent[cur_mask][cur_loc]
        itinerary.append({
            "action": "meet",
            "location": locations[friends[j]["location"]],
            "person": friends[j]["name"],
            "start_time": format_time(start_meeting),
            "end_time": format_time(end_meeting)
        })
        cur_mask = prev_mask
        cur_loc = prev_loc
    
    itinerary.reverse()
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()