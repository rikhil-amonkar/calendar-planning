import json

def main():
    # Define the locations and create a mapping to indices
    locations = [
        "Chinatown",
        "Embarcadero",
        "Pacific Heights",
        "Russian Hill",
        "Haight-Ashbury",
        "Golden Gate Park",
        "Fisherman's Wharf",
        "Sunset District",
        "The Castro"
    ]
    location_index_map = {loc: idx for idx, loc in enumerate(locations)}
    
    # Define travel times dictionary
    travel_times = {
        "Chinatown": {
            "Embarcadero": 5,
            "Pacific Heights": 10,
            "Russian Hill": 7,
            "Haight-Ashbury": 19,
            "Golden Gate Park": 23,
            "Fisherman's Wharf": 8,
            "Sunset District": 29,
            "The Castro": 22
        },
        "Embarcadero": {
            "Chinatown": 7,
            "Pacific Heights": 11,
            "Russian Hill": 8,
            "Haight-Ashbury": 21,
            "Golden Gate Park": 25,
            "Fisherman's Wharf": 6,
            "Sunset District": 30,
            "The Castro": 25
        },
        "Pacific Heights": {
            "Chinatown": 11,
            "Embarcadero": 10,
            "Russian Hill": 7,
            "Haight-Ashbury": 11,
            "Golden Gate Park": 15,
            "Fisherman's Wharf": 13,
            "Sunset District": 21,
            "The Castro": 16
        },
        "Russian Hill": {
            "Chinatown": 9,
            "Embarcadero": 8,
            "Pacific Heights": 7,
            "Haight-Ashbury": 17,
            "Golden Gate Park": 21,
            "Fisherman's Wharf": 7,
            "Sunset District": 23,
            "The Castro": 21
        },
        "Haight-Ashbury": {
            "Chinatown": 19,
            "Embarcadero": 20,
            "Pacific Heights": 12,
            "Russian Hill": 17,
            "Golden Gate Park": 7,
            "Fisherman's Wharf": 23,
            "Sunset District": 15,
            "The Castro": 6
        },
        "Golden Gate Park": {
            "Chinatown": 23,
            "Embarcadero": 25,
            "Pacific Heights": 16,
            "Russian Hill": 19,
            "Haight-Ashbury": 7,
            "Fisherman's Wharf": 24,
            "Sunset District": 10,
            "The Castro": 13
        },
        "Fisherman's Wharf": {
            "Chinatown": 12,
            "Embarcadero": 8,
            "Pacific Heights": 12,
            "Russian Hill": 7,
            "Haight-Ashbury": 22,
            "Golden Gate Park": 25,
            "Sunset District": 27,
            "The Castro": 27
        },
        "Sunset District": {
            "Chinatown": 30,
            "Embarcadero": 30,
            "Pacific Heights": 21,
            "Russian Hill": 24,
            "Haight-Ashbury": 15,
            "Golden Gate Park": 11,
            "Fisherman's Wharf": 29,
            "The Castro": 17
        },
        "The Castro": {
            "Chinatown": 22,
            "Embarcadero": 22,
            "Pacific Heights": 16,
            "Russian Hill": 18,
            "Haight-Ashbury": 6,
            "Golden Gate Park": 11,
            "Fisherman's Wharf": 24,
            "Sunset District": 17
        }
    }
    
    # Define friends with their constraints (times in minutes from midnight)
    friends = [
        {"name": "Richard", "location": "Embarcadero", "start": 15*60+15, "end": 18*60+45, "min_dur": 90},
        {"name": "Mark", "location": "Pacific Heights", "start": 15*60+0, "end": 17*60+0, "min_dur": 45},
        {"name": "Matthew", "location": "Russian Hill", "start": 17*60+30, "end": 21*60+0, "min_dur": 90},
        {"name": "Rebecca", "location": "Haight-Ashbury", "start": 14*60+45, "end": 18*60+0, "min_dur": 60},
        {"name": "Melissa", "location": "Golden Gate Park", "start": 13*60+45, "end": 17*60+30, "min_dur": 90},
        {"name": "Margaret", "location": "Fisherman's Wharf", "start": 14*60+45, "end": 20*60+15, "min_dur": 15},
        {"name": "Emily", "location": "Sunset District", "start": 15*60+45, "end": 17*60+0, "min_dur": 45},
        {"name": "George", "location": "The Castro", "start": 14*60+0, "end": 16*60+15, "min_dur": 75}
    ]
    
    n = len(friends)  # 8 friends
    num_locations = len(locations)  # 9 locations
    
    # Initialize DP table and parent table
    dp = [[10**9] * num_locations for _ in range(1 << n)]
    parent = [[None] * num_locations for _ in range(1 << n)]  # (prev_mask, prev_loc, friend_index, start_time, end_time)
    
    # Base state: start at Chinatown (index 0) at 9:00 (540 minutes)
    dp[0][0] = 540
    
    # Iterate over all masks
    for mask in range(1 << n):
        for loc_idx in range(num_locations):
            current_time = dp[mask][loc_idx]
            if current_time == 10**9:
                continue
            current_loc = locations[loc_idx]
            
            # Try each friend not yet visited
            for friend_idx in range(n):
                if mask & (1 << friend_idx):
                    continue
                friend = friends[friend_idx]
                next_loc = friend["location"]
                
                # Get travel time from current_loc to next_loc
                travel_time = travel_times[current_loc][next_loc]
                arrival_time = current_time + travel_time
                start_time = max(arrival_time, friend["start"])
                end_time = start_time + friend["min_dur"]
                
                # Check if meeting is feasible within the friend's window
                if end_time <= friend["end"]:
                    new_mask = mask | (1 << friend_idx)
                    new_loc_idx = location_index_map[next_loc]
                    
                    # Update DP state if we found a better (earlier) end time
                    if end_time < dp[new_mask][new_loc_idx]:
                        dp[new_mask][new_loc_idx] = end_time
                        parent[new_mask][new_loc_idx] = (mask, loc_idx, friend_idx, start_time, end_time)
    
    # Find the best state (mask with maximum meetings)
    best_mask = 0
    best_count = 0
    best_loc_idx = 0
    for mask in range(1 << n):
        count = bin(mask).count("1")
        for loc_idx in range(num_locations):
            if dp[mask][loc_idx] < 10**9:
                if count > best_count:
                    best_count = count
                    best_mask = mask
                    best_loc_idx = loc_idx
                if best_count == n:  # Found a schedule with all friends
                    break
        if best_count == n:
            break
    
    # Backtrack to build itinerary
    itinerary = []
    current_mask = best_mask
    current_loc_idx = best_loc_idx
    
    def format_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h}:{m:02d}"
    
    while current_mask != 0:
        if parent[current_mask][current_loc_idx] is None:
            break
        prev_mask, prev_loc_idx, friend_idx, start_time, end_time = parent[current_mask][current_loc_idx]
        friend = friends[friend_idx]
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": format_time(start_time),
            "end_time": format_time(end_time)
        })
        current_mask = prev_mask
        current_loc_idx = prev_loc_idx
    
    # Reverse to get chronological order
    itinerary.reverse()
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()