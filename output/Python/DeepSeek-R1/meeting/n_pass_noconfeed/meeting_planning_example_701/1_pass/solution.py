import json

def min_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Define location names and mapping
    loc_names = [
        'Mission District', 
        'The Castro', 
        'Nob Hill', 
        'Presidio', 
        'Marina District', 
        'Pacific Heights', 
        'Golden Gate Park', 
        'Chinatown', 
        'Richmond District'
    ]
    loc_to_index = {name: idx for idx, name in enumerate(loc_names)}
    
    # Travel times dictionary (from input)
    travel_times = {
        "Mission District": {
            "The Castro": 7, "Nob Hill": 12, "Presidio": 25, "Marina District": 19,
            "Pacific Heights": 16, "Golden Gate Park": 17, "Chinatown": 16, "Richmond District": 20
        },
        "The Castro": {
            "Mission District": 7, "Nob Hill": 16, "Presidio": 20, "Marina District": 21,
            "Pacific Heights": 16, "Golden Gate Park": 11, "Chinatown": 22, "Richmond District": 16
        },
        "Nob Hill": {
            "Mission District": 13, "The Castro": 17, "Presidio": 17, "Marina District": 11,
            "Pacific Heights": 8, "Golden Gate Park": 17, "Chinatown": 6, "Richmond District": 14
        },
        "Presidio": {
            "Mission District": 26, "The Castro": 21, "Nob Hill": 18, "Marina District": 11,
            "Pacific Heights": 11, "Golden Gate Park": 12, "Chinatown": 21, "Richmond District": 7
        },
        "Marina District": {
            "Mission District": 20, "The Castro": 22, "Nob Hill": 12, "Presidio": 10,
            "Pacific Heights": 7, "Golden Gate Park": 18, "Chinatown": 15, "Richmond District": 11
        },
        "Pacific Heights": {
            "Mission District": 15, "The Castro": 16, "Nob Hill": 8, "Presidio": 11,
            "Marina District": 6, "Golden Gate Park": 15, "Chinatown": 11, "Richmond District": 12
        },
        "Golden Gate Park": {
            "Mission District": 17, "The Castro": 13, "Nob Hill": 20, "Presidio": 11,
            "Marina District": 16, "Pacific Heights": 16, "Chinatown": 23, "Richmond District": 7
        },
        "Chinatown": {
            "Mission District": 17, "The Castro": 22, "Nob Hill": 9, "Presidio": 19,
            "Marina District": 12, "Pacific Heights": 10, "Golden Gate Park": 23, "Richmond District": 20
        },
        "Richmond District": {
            "Mission District": 20, "The Castro": 16, "Nob Hill": 17, "Presidio": 7,
            "Marina District": 9, "Pacific Heights": 10, "Golden Gate Park": 9, "Chinatown": 20
        }
    }
    
    # Create travel matrix (9x9)
    travel = [[0]*9 for _ in range(9)]
    for i in range(9):
        from_loc = loc_names[i]
        for j in range(9):
            to_loc = loc_names[j]
            if from_loc == to_loc:
                travel[i][j] = 0
            else:
                travel[i][j] = travel_times[from_loc][to_loc]
    
    # Define friends with their constraints (times in minutes since midnight)
    friends = [
        {'name': 'Lisa', 'location': 'The Castro', 'start': 19*60+15, 'end': 21*60+15, 'min_dur': 120},
        {'name': 'Daniel', 'location': 'Nob Hill', 'start': 8*60+15, 'end': 11*60, 'min_dur': 15},
        {'name': 'Elizabeth', 'location': 'Presidio', 'start': 21*60+15, 'end': 22*60+15, 'min_dur': 45},
        {'name': 'Steven', 'location': 'Marina District', 'start': 16*60+30, 'end': 20*60+45, 'min_dur': 90},
        {'name': 'Timothy', 'location': 'Pacific Heights', 'start': 12*60, 'end': 18*60, 'min_dur': 90},
        {'name': 'Ashley', 'location': 'Golden Gate Park', 'start': 20*60+45, 'end': 21*60+45, 'min_dur': 60},
        {'name': 'Kevin', 'location': 'Chinatown', 'start': 12*60, 'end': 19*60, 'min_dur': 30},
        {'name': 'Betty', 'location': 'Richmond District', 'start': 13*60+15, 'end': 15*60+45, 'min_dur': 30}
    ]
    
    # Precompute location index for each friend
    friend_loc_index = [loc_to_index[f['location']] for f in friends]
    
    # Initialize DP table and parent
    n = len(friends)  # 8
    num_masks = 1 << n
    INF = 10**9
    dp = [[INF] * 9 for _ in range(num_masks)]
    parent = [[None] * 9 for _ in range(num_masks)]  # (prev_mask, prev_loc, friend_index, meeting_start)
    
    # Start state: mask 0, at Mission District (index 0) at 9:00 (540 minutes)
    dp[0][0] = 540
    
    # DP iteration
    for mask in range(num_masks):
        for loc_i in range(9):
            if dp[mask][loc_i] == INF:
                continue
            for j in range(n):
                if mask & (1 << j):
                    continue
                loc_j = friend_loc_index[j]
                travel_time = travel[loc_i][loc_j]
                arrival = dp[mask][loc_i] + travel_time
                meeting_start = max(arrival, friends[j]['start'])
                meeting_end = meeting_start + friends[j]['min_dur']
                if meeting_end > friends[j]['end']:
                    continue
                new_mask = mask | (1 << j)
                if meeting_end < dp[new_mask][loc_j]:
                    dp[new_mask][loc_j] = meeting_end
                    parent[new_mask][loc_j] = (mask, loc_i, j, meeting_start)
    
    # Find best state (maximize number of meetings, then minimize end time)
    best_mask = 0
    best_count = -1
    best_time = INF
    best_loc = None
    for mask in range(num_masks):
        count = bin(mask).count("1")
        for loc in range(9):
            if dp[mask][loc] < INF:
                if count > best_count or (count == best_count and dp[mask][loc] < best_time):
                    best_count = count
                    best_time = dp[mask][loc]
                    best_mask = mask
                    best_loc = loc
    
    # Reconstruct itinerary
    itinerary = []
    mask = best_mask
    loc = best_loc
    while mask != 0:
        if parent[mask][loc] is None:
            break
        prev_mask, prev_loc, j, meeting_start = parent[mask][loc]
        meeting_end = meeting_start + friends[j]['min_dur']
        event = {
            "action": "meet",
            "location": friends[j]['location'],
            "person": friends[j]['name'],
            "start_time": min_to_time(meeting_start),
            "end_time": min_to_time(meeting_end)
        }
        itinerary.append(event)
        mask = prev_mask
        loc = prev_loc
    
    itinerary.reverse()
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()