import json

def main():
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
    
    friends_rel = []
    for (name, loc, start_abs, end_abs, dur) in friends_abs:
        start_rel = start_abs - 540
        end_rel = end_abs - 540
        friends_rel.append((name, loc, start_rel, end_rel, dur))
    
    n = len(friends_rel)
    total_states = 1 << n
    max_total_time = 660  # 11 hours (9am-8pm) in minutes from 9am
    
    dp = {}
    dp[(0, "Presidio")] = (0, None)
    
    for mask in range(total_states):
        for loc in travel_times:
            state_key = (mask, loc)
            if state_key not in dp:
                continue
            current_time, parent_info = dp[state_key]
            for i in range(n):
                if mask & (1 << i):
                    continue
                f_name, f_loc, f_start, f_end, dur = friends_rel[i]
                if loc not in travel_times or f_loc not in travel_times[loc]:
                    continue
                travel_time = travel_times[loc][f_loc]
                arrival = current_time + travel_time
                if arrival < f_start:
                    continue
                start_meeting = arrival
                end_meeting = start_meeting + dur
                if end_meeting > f_end:
                    continue
                if end_meeting + travel_times[f_loc]["Presidio"] > max_total_time:
                    continue
                new_mask = mask | (1 << i)
                new_state_key = (new_mask, f_loc)
                new_time = end_meeting
                if new_state_key not in dp or new_time < dp[new_state_key][0]:
                    parent_info_new = (mask, loc, i, start_meeting, end_meeting)
                    dp[new_state_key] = (new_time, parent_info_new)
    
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
    
    meetings = []
    current_state_key = best_state_key
    current_parent_info = best_parent_info
    
    while current_parent_info is not None:
        mask, loc, i, start_meeting, end_meeting = current_parent_info
        f_name, f_loc, _, _, _ = friends_rel[i]
        abs_start = 540 + start_meeting
        abs_end = 540 + end_meeting
        hour_s = abs_start // 60
        min_s = abs_start % 60
        hour_e = abs_end // 60
        min_e = abs_end % 60
        start_str = f"{hour_s}:{min_s:02d}"
        end_str = f"{hour_e}:{min_e:02d}"
        meetings.append({
            "location": f_loc,
            "person": f_name,
            "start_time": start_str,
            "end_time": end_str
        })
        prev_key = (mask, loc)
        if prev_key in dp:
            _, current_parent_info = dp[prev_key]
        else:
            current_parent_info = None
    
    meetings.reverse()
    
    def abs_to_time_str(abstime):
        hour = abstime // 60
        minute = abstime % 60
        return f"{hour}:{minute:02d}"
    
    full_itinerary = []
    current_location = "Presidio"
    current_time_abs = 540
    
    for meet in meetings:
        # Travel to meeting
        travel_time = travel_times[current_location][meet["location"]]
        end_travel_abs = current_time_abs + travel_time
        travel_seg = {
            "action": "travel",
            "from": current_location,
            "to": meet["location"],
            "start_time": abs_to_time_str(current_time_abs),
            "end_time": abs_to_time_str(end_travel_abs)
        }
        full_itinerary.append(travel_seg)
        
        # Meeting
        meet_start_abs = max(end_travel_abs, int(meet["start_time"].split(':')[0])*60 + int(meet["start_time"].split(':')[1]))
        meet_end_abs = meet_start_abs + (int(meet["end_time"].split(':')[0])*60 + int(meet["end_time"].split(':')[1]) - 
                                        int(meet["start_time"].split(':')[0])*60 - int(meet["start_time"].split(':')[1]))
        meet_seg = {
            "action": "meet",
            "location": meet["location"],
            "person": meet["person"],
            "start_time": abs_to_time_str(meet_start_abs),
            "end_time": abs_to_time_str(meet_end_abs)
        }
        full_itinerary.append(meet_seg)
        
        current_location = meet["location"]
        current_time_abs = meet_end_abs
    
    # Return to Presidio
    if current_location != "Presidio":
        travel_time_last = travel_times[current_location]["Presidio"]
        end_travel_last_abs = current_time_abs + travel_time_last
        travel_seg_last = {
            "action": "travel",
            "from": current_location,
            "to": "Presidio",
            "start_time": abs_to_time_str(current_time_abs),
            "end_time": abs_to_time_str(end_travel_last_abs)
        }
        full_itinerary.append(travel_seg_last)
    
    result = {"itinerary": full_itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()