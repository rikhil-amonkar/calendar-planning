import json

def main():
    # Travel times dictionary (in minutes)
    travel_times = {
        "Presidio": {"Haight-Ashbury": 15, "Nob Hill": 18, "Russian Hill": 14, "North Beach": 18, "Chinatown": 21, "Union Square": 22, "Embarcadero": 20, "Financial District": 23, "Marina District": 11},
        "Haight-Ashbury": {"Presidio": 15, "Nob Hill": 15, "Russian Hill": 17, "North Beach": 19, "Chinatown": 19, "Union Square": 19, "Embarcadero": 20, "Financial District": 21, "Marina District": 17},
        "Nob Hill": {"Presidio": 17, "Haight-Ashbury": 13, "Russian Hill": 5, "North Beach": 8, "Chinatown": 6, "Union Square": 7, "Embarcadero": 9, "Financial District": 9, "Marina District": 11},
        "Russian Hill": {"Presidio": 14, "Haight-Ashbury": 17, "Nob Hill": 5, "North Beach": 5, "Chinatown": 9, "Union Square": 10, "Embarcadero": 8, "Financial District": 11, "Marina District": 7},
        "North Beach": {"Presidio": 17, "Haight-Ashbury": 18, "Nob Hill": 7, "Russian Hill": 4, "Chinatown": 6, "Union Square": 7, "Embarcadero": 6, "Financial District": 8, "Marina District": 9},
        "Chinatown": {"Presidio": 19, "Haight-Ashbury": 19, "Nob Hill": 9, "Russian Hill": 7, "North Beach": 3, "Union Square": 7, "Embarcadero": 5, "Financial District": 5, "Marina District": 12},
        "Union Square": {"Presidio": 24, "Haight-Ashbury": 18, "Nob Hill": 9, "Russian Hill": 13, "North Beach": 10, "Chinatown": 7, "Embarcadero": 11, "Financial District": 9, "Marina District": 18},
        "Embarcadero": {"Presidio": 20, "Haight-Ashbury": 21, "Nob Hill": 10, "Russian Hill": 8, "North Beach": 5, "Chinatown": 7, "Union Square": 10, "Financial District": 5, "Marina District": 12},
        "Financial District": {"Presidio": 22, "Haight-Ashbury": 19, "Nob Hill": 8, "Russian Hill": 11, "North Beach": 7, "Chinatown": 5, "Union Square": 9, "Embarcadero": 4, "Marina District": 15},
        "Marina District": {"Presidio": 10, "Haight-Ashbury": 16, "Nob Hill": 12, "Russian Hill": 8, "North Beach": 11, "Chinatown": 15, "Union Square": 16, "Embarcadero": 14, "Financial District": 17}
    }
    
    # Friends data: (name, location, start_avail_abs, end_avail_abs, min_duration)
    # Times in absolute minutes from midnight
    friends_abs = [
        ("Karen", "Haight-Ashbury", 21*60, 21*60+45, 45),
        ("Jessica", "Nob Hill", 13*60+45, 21*60, 90),
        ("Brian", "Russian Hill", 15*60+30, 21*60+45, 60),
        ("Kenneth", "North Beach", 9*60+45, 21*60, 30),
        ("Jason", "Chinatown", 8*60+15, 11*60+45, 75),
        ("Stephanie", "Union Square", 14*60+45, 18*60+45, 105),
        ("Kimberly", "Embarcadero", 9*60+45, 19*60+30, 75),
        ("Steven", "Financial District", 7*60+15, 21*60+15, 60),
        ("Mark", "Marina District", 10*60+15, 13*60, 75)
    ]
    
    # Convert to relative times from 9:00 AM (which is 540 minutes from midnight)
    friends_rel = []
    for (name, loc, start_abs, end_abs, dur) in friends_abs:
        start_rel = start_abs - 540  # can be negative
        end_rel = end_abs - 540
        friends_rel.append((name, loc, start_rel, end_rel, dur))
    
    all_locations = list(travel_times.keys())
    n = len(friends_rel)
    total_states = 1 << n
    
    # DP: key: (mask, location) -> (min_time, parent_info)
    # parent_info: (prev_mask, prev_location, friend_index, start_meeting, end_meeting)
    dp = {}
    # Initialize: start at Presidio at time 0
    dp[(0, "Presidio")] = (0, None)
    
    # Iterate over all masks
    for mask in range(total_states):
        for loc in all_locations:
            state_key = (mask, loc)
            if state_key not in dp:
                continue
            current_time, parent_info = dp[state_key]
            # Try to extend to each friend not yet visited
            for i in range(n):
                if mask & (1 << i):
                    continue
                f = friends_rel[i]
                f_name, f_loc, f_start_rel, f_end_rel, dur = f
                # Skip if no travel time defined (shouldn't happen)
                if loc not in travel_times or f_loc not in travel_times[loc]:
                    continue
                travel_time = travel_times[loc][f_loc]
                arrival = current_time + travel_time
                # Enforce no waiting: must arrive at or after friend's available time
                if arrival < f_start_rel:
                    continue
                start_meeting = arrival
                end_meeting = start_meeting + dur
                # Check if meeting can be scheduled within the friend's availability
                if end_meeting > f_end_rel:
                    continue
                new_mask = mask | (1 << i)
                new_loc = f_loc
                new_state_key = (new_mask, new_loc)
                new_time = end_meeting
                # Update DP state if it's the first time or we found a better (earlier) time
                if new_state_key not in dp or new_time < dp[new_state_key][0]:
                    parent_info_new = (mask, loc, i, start_meeting, end_meeting)
                    dp[new_state_key] = (new_time, parent_info_new)
    
    # Find the best state: maximum number of meetings (popcount in mask)
    best_count = -1
    best_state_key = None
    best_time = None
    best_parent_info = None
    
    for state_key, (time_val, parent_info) in dp.items():
        mask, loc = state_key
        count = bin(mask).count("1")
        if count > best_count or (count == best_count and time_val < best_time):
            best_count = count
            best_state_key = state_key
            best_time = time_val
            best_parent_info = parent_info
    
    # Backtrack to get itinerary
    itinerary_list = []
    current_state_key = best_state_key
    current_parent_info = best_parent_info
    
    while current_parent_info is not None:
        mask, loc, i, start_meeting, end_meeting = current_parent_info
        f_name, f_loc, _, _, _ = friends_rel[i]
        # Convert relative times to absolute (minutes from midnight)
        abs_start = 540 + start_meeting
        abs_end = 540 + end_meeting
        hour_s = abs_start // 60
        min_s = abs_start % 60
        hour_e = abs_end // 60
        min_e = abs_end % 60
        start_str = f"{hour_s}:{min_s:02d}"
        end_str = f"{hour_e}:{min_e:02d}"
        itinerary_list.append({
            "action": "meet",
            "location": f_loc,
            "person": f_name,
            "start_time": start_str,
            "end_time": end_str
        })
        # Move to previous state
        prev_key = (mask, loc)
        if prev_key in dp:
            _, current_parent_info = dp[prev_key]
        else:
            current_parent_info = None
    
    # Reverse to get chronological order
    itinerary_list.reverse()
    
    # Helper functions for time conversion
    def time_str_to_abs(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        return hour * 60 + minute

    def abs_to_time_str(abstime):
        hour = abstime // 60
        minute = abstime % 60
        return f"{hour}:{minute:02d}"

    # Build full itinerary including travel segments
    full_itinerary = []

    if itinerary_list:
        # First travel: from Presidio to first meeting location
        first_meeting = itinerary_list[0]
        travel_time0 = travel_times["Presidio"][first_meeting["location"]]
        start_abs0 = 540  # 9:00 AM
        end_abs0 = start_abs0 + travel_time0
        travel_seg0 = {
            "action": "travel",
            "from": "Presidio",
            "to": first_meeting["location"],
            "start_time": abs_to_time_str(start_abs0),
            "end_time": abs_to_time_str(end_abs0)
        }
        full_itinerary.append(travel_seg0)
        full_itinerary.append(first_meeting)

        # For each subsequent meeting
        for i in range(1, len(itinerary_list)):
            prev_meeting = itinerary_list[i-1]
            curr_meeting = itinerary_list[i]
            travel_time_i = travel_times[prev_meeting["location"]][curr_meeting["location"]]
            # Start travel at the end time of the previous meeting
            start_travel_abs = time_str_to_abs(prev_meeting["end_time"])
            end_travel_abs = start_travel_abs + travel_time_i
            travel_seg = {
                "action": "travel",
                "from": prev_meeting["location"],
                "to": curr_meeting["location"],
                "start_time": prev_meeting["end_time"],
                "end_time": abs_to_time_str(end_travel_abs)
            }
            full_itinerary.append(travel_seg)
            full_itinerary.append(curr_meeting)

        # Last travel: from last meeting location to Presidio
        last_meeting = itinerary_list[-1]
        travel_time_last = travel_times[last_meeting["location"]]["Presidio"]
        start_travel_last_abs = time_str_to_abs(last_meeting["end_time"])
        end_travel_last_abs = start_travel_last_abs + travel_time_last
        travel_seg_last = {
            "action": "travel",
            "from": last_meeting["location"],
            "to": "Presidio",
            "start_time": last_meeting["end_time"],
            "end_time": abs_to_time_str(end_travel_last_abs)
        }
        full_itinerary.append(travel_seg_last)

    # Output as JSON
    result = {
        "itinerary": full_itinerary
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()